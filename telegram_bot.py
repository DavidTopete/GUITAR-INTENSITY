"""telegram_bot.py - Gear News: bot unificado de noticias para Telegram.

Reemplaza al telegram_bot.py anterior (Guitar Gear News) y al bot de bajo.
Cubre guitarra, bajo, teclados, bateria y pro audio, publica en temas de un
supergrupo segun un calendario semanal y no repite noticias.

COMPATIBILIDAD CON EL BOT ANTERIOR
  - Mismo nombre de archivo y mismas variables de entorno: TOKEN, CHAT_ID.
  - Usa tu traductor.py (debe estar en la misma carpeta), con la misma interfaz.
  - `python telegram_bot.py` sin argumentos = recolectar + publicar (diario).
  - Importa en cada ejecucion noticias_enviadas.json y
    noticias_enviadas_bass.json: nada de lo ya enviado se vuelve a publicar.
  - Sigue escribiendo noticias_enviadas.json (lista de URLs). Si tu despliegue
    solo versiona ese archivo, tampoco se repiten noticias.
  - La configuracion va integrada al final del archivo (CONFIG_INTEGRADA).
    Si existe un config.yaml en la carpeta, tiene prioridad (requiere PyYAML).

ESTADO NUEVO QUE CONVIENE VERSIONAR / CONSERVAR
  - gear_news.db (SQLite): pool de noticias pendientes, grupos de duplicados,
    historial y estado de los feeds. Sin el, el calendario solo dispone de lo
    que haya en los feeds el dia de publicar (funciona, pero peor).

DEPENDENCIAS
  pip install requests feedparser beautifulsoup4      (PyYAML solo si usas config.yaml)

USO
  python telegram_bot.py                      # diario: recolectar + publicar
  python telegram_bot.py recolectar           # solo leer feeds (ideal cada 6 h)
  python telegram_bot.py publicar             # destacadas + calendario del dia
  python telegram_bot.py diario --dry-run     # simula: imprime, no envia ni guarda
  python telegram_bot.py validar-feeds        # comprueba todas las URLs
  python telegram_bot.py crear-temas          # crea los temas del foro y muestra sus IDs
  python telegram_bot.py estado               # resumen del pool y feeds con fallos
  python telegram_bot.py migrar a.json b.json # importa historiales adicionales
  Opciones: --dia lunes  --sin-traduccion (con --dry-run)  --config RUTA  -v

Archivo generado a partir de los modulos del paquete gear_news (nucleo/*.py y
main.py). Las secciones conservan el nombre del modulo de origen.
"""

import argparse
import copy
import html
import importlib
import json
import logging
import os
import re
import socket
import sqlite3
import sys
import time
import unicodedata
import xml.etree.ElementTree as ET
from collections import Counter
from contextlib import contextmanager
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from urllib.parse import parse_qsl, urlencode, urlsplit, urlunsplit
from zoneinfo import ZoneInfo

import requests
from bs4 import BeautifulSoup

# Alias de modulo: el codigo de origen usa feeds.x / feeds_mod.x / config_mod.x
feeds = feeds_mod = config_mod = sys.modules[__name__]


# =============================================================================
# texto
#   Utilidades de texto: normalizacion de URLs, limpieza de HTML, tokens de
#   titulo para detectar duplicados y escapado seguro para Telegram (HTML).
# =============================================================================

# ---------------------------------------------------------------------------
# URLs
# ---------------------------------------------------------------------------

_PARAMS_RASTREO_PREFIJOS = ("utm_", "mc_", "_hs", "oly_")
_PARAMS_RASTREO = {"fbclid", "gclid", "dclid", "igshid", "yclid", "msclkid",
                   "ref_src", "cmpid", "ito", "rss", "feed", "src"}


def normalizar_url(url):
    """Clave canonica de una URL para deduplicar.

    - esquema siempre https (http/https son la misma noticia)
    - host en minusculas y sin 'www.'
    - sin fragmento, sin barra final, sin parametros de rastreo
    - parametros restantes ordenados
    """
    if not url:
        return ""
    p = urlsplit(url.strip())
    host = p.netloc.lower()
    if host.startswith("www."):
        host = host[4:]
    ruta = re.sub(r"/{2,}", "/", p.path).rstrip("/") or "/"
    params = [
        (k, v) for k, v in parse_qsl(p.query, keep_blank_values=False)
        if k.lower() not in _PARAMS_RASTREO
        and not k.lower().startswith(_PARAMS_RASTREO_PREFIJOS)
    ]
    query = urlencode(sorted(params))
    return urlunsplit(("https", host, ruta, query, ""))


# ---------------------------------------------------------------------------
# Limpieza
# ---------------------------------------------------------------------------

_RE_ESPACIOS = re.compile(r"\s+")
_RE_PIES = [
    re.compile(r"\s*The post .+? appeared first on .+?\.?\s*$", re.I | re.S),
    re.compile(r"\s*La entrada .+? se public[oó] primero en .+?\.?\s*$", re.I | re.S),
    re.compile(r"\s*(Continue reading|Read more|Leer m[aá]s|Seguir leyendo)\b.*$", re.I | re.S),
    re.compile(r"\s*\[(…|\.\.\.|&hellip;)\]\s*$"),
]
_RE_MURO_PAGO = re.compile(
    r"(to read the full story|subscribe to access|subscribers only|"
    r"premium content|para leer la nota completa)", re.I)


def limpiar_html(texto):
    if not texto:
        return ""
    plano = BeautifulSoup(texto, "html.parser").get_text(" ", strip=True)
    return _RE_ESPACIOS.sub(" ", plano).strip()


def limpiar_resumen(texto):
    """Quita pies de WordPress, 'leer mas' y avisos de muro de pago."""
    texto = limpiar_html(texto)
    for patron in _RE_PIES:
        texto = patron.sub("", texto)
    texto = texto.strip()
    if _RE_MURO_PAGO.search(texto) and len(texto) < 400:
        # Resumen que es solo el aviso de suscripcion: no aporta nada.
        return ""
    return texto


def truncar(texto, maximo, sufijo="…"):
    """Recorta en limite de palabra."""
    if not texto or len(texto) <= maximo:
        return texto or ""
    corte = texto[:maximo]
    espacio = corte.rfind(" ")
    if espacio > maximo * 0.6:
        corte = corte[:espacio]
    return corte.rstrip(" ,;:.-–—") + sufijo


def contiene_japones(texto):
    if not texto:
        return False
    return any(
        "぀" <= c <= "ヿ" or "㐀" <= c <= "䶿" or "一" <= c <= "鿿"
        for c in texto
    )


# ---------------------------------------------------------------------------
# Comparacion de titulos
# ---------------------------------------------------------------------------

def sin_acentos(texto):
    """Minusculas y sin diacriticos (solo para comparar, nunca para mostrar)."""
    if not texto:
        return ""
    nfkd = unicodedata.normalize("NFKD", texto.lower())
    return "".join(c for c in nfkd if not unicodedata.combining(c))


_STOPWORDS = set("""
a an and are as at be by for from has have how in into is it its of on or our
that the their this to was were what when who why will with you your vs via
new news announces announced unveils unveiled launches launched launch reveals
introduces introduced releases released debuts here now just first look
review video watch exclusive update updates official latest best more get gets
el la los las un una unos unas de del al y o en con por para que se su sus es
nuevo nueva nuevos nuevas presenta anuncia lanza lanzamiento revela
""".split())

_RE_TOKEN = re.compile(r"\w+", re.UNICODE)


def tokens_titulo(titulo):
    """Conjunto de tokens significativos de un titulo."""
    t = sin_acentos(titulo).replace("’", "'")
    t = re.sub(r"'s\b", "", t)
    tokens = set()
    for tok in _RE_TOKEN.findall(t):
        if tok in _STOPWORDS:
            continue
        if len(tok) < 2 and not tok.isdigit():
            continue
        tokens.add(tok)
    return tokens


def serializar_tokens(tokens):
    return " ".join(sorted(tokens))


def deserializar_tokens(texto):
    return set(texto.split()) if texto else set()


def titulos_similares(a, b, umbral_jaccard=0.7, umbral_solapamiento=0.8,
                      min_comunes=3):
    """Decide si dos conjuntos de tokens describen la misma noticia.

    Dos criterios (basta uno):
    - Jaccard >= umbral_jaccard
    - Solapamiento (|A∩B| / min(|A|,|B|)) >= umbral_solapamiento con al
      menos `min_comunes` tokens en comun. Cubre el caso tipico de un medio
      con titulo corto y otro con titulo largo sobre el mismo producto.

    Titulos muy cortos solo se agrupan si son identicos, para no fusionar
    noticias distintas que comparten dos palabras genericas.
    """
    if not a or not b:
        return False
    comunes = len(a & b)
    if min(len(a), len(b)) < min_comunes:
        # Titulos muy cortos: solo si son identicos y no de una sola palabra.
        return a == b and len(a) >= 2
    solo_a, solo_b = a - b, b - a
    # Modelos distintos: 'Pigments 5' vs 'Pigments 6', 'MODX M6' vs 'MODX M8'.
    if any(_tiene_digito(t) for t in solo_a) and any(_tiene_digito(t) for t in solo_b):
        return False
    # Uno contiene (casi) al otro: titulo corto vs titulo largo de la misma noticia.
    solapamiento = comunes / min(len(a), len(b))
    if comunes >= min_comunes and solapamiento >= umbral_solapamiento:
        return True
    # Ambos tienen palabras exclusivas ('Stratocaster' vs 'Telecaster'):
    # se exige un parecido global alto.
    return comunes / len(a | b) >= umbral_jaccard


def _tiene_digito(token):
    return any(c.isdigit() for c in token)


# ---------------------------------------------------------------------------
# Telegram
# ---------------------------------------------------------------------------

def escape(texto):
    """Escapado para parse_mode=HTML (Telegram admite entidades numericas)."""
    return html.escape(texto or "", quote=True)


def hashtag(texto):
    """'Allen & Heath' -> 'allenheath'. Devuelve '' si no es valido."""
    limpio = re.sub(r"[^\w]", "", sin_acentos(texto))
    if not limpio:
        return ""
    if not limpio[0].isalpha():
        limpio = "x" + limpio
    return limpio


# =============================================================================
# feeds
#   Descarga y parseo de feeds.
#
#   Usa feedparser si esta instalado (recomendado). Si no, recurre a un parser
#   RSS 2.0 / Atom basico con la libreria estandar, suficiente para feeds de
#   WordPress y similares.
#
#   Nunca se descarga un feed sin timeout: el fallback `feedparser.parse(url)`
#   de los bots anteriores se eliminó porque podia colgar la ejecucion.
# =============================================================================

log = logging.getLogger("gear_news.feeds")

HEADERS_HTTP = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
    ),
    "Accept": "application/rss+xml, application/atom+xml, application/xml;q=0.9, */*;q=0.8",
}


@dataclass
class Entrada:
    titulo: str
    link: str
    resumen: str = ""
    contenido: str = ""
    fecha: datetime | None = None


class ErrorFeed(Exception):
    pass


# ---------------------------------------------------------------------------
# Descarga
# ---------------------------------------------------------------------------

def descargar(url, timeout=15):
    try:
        r = requests.get(url, headers=HEADERS_HTTP, timeout=timeout)
        r.raise_for_status()
        return r.content
    except requests.exceptions.HTTPError as e:
        raise ErrorFeed(f"HTTP {e.response.status_code}") from None
    except requests.exceptions.RequestException as e:
        # Solo el tipo: el mensaje completo puede ser muy largo.
        raise ErrorFeed(type(e).__name__) from None


def leer_fuente(url, timeout=15):
    """Devuelve (entradas, error). error es None si todo fue bien."""
    try:
        contenido = descargar(url, timeout)
        entradas = parsear(contenido)
    except ErrorFeed as e:
        return [], str(e)
    except Exception as e:  # feed corrupto u otro problema inesperado
        log.exception(f"Error parseando {url}")
        return [], f"parseo: {type(e).__name__}"
    if not entradas:
        return [], "feed sin entradas"
    return entradas, None


# ---------------------------------------------------------------------------
# Parseo
# ---------------------------------------------------------------------------

def parsear(contenido):
    try:
        import feedparser  # noqa: F401
    except ImportError:
        return _parsear_basico(contenido)
    return _parsear_feedparser(contenido)


def _fecha_struct(struct):
    if not struct:
        return None
    try:
        return datetime(*struct[:6], tzinfo=timezone.utc)
    except (TypeError, ValueError):
        return None


def _parsear_feedparser(contenido):
    import feedparser

    feed = feedparser.parse(contenido)
    if feed.bozo and not feed.entries:
        raise ErrorFeed(f"feed invalido: {type(feed.bozo_exception).__name__}")

    entradas = []
    for e in feed.entries:
        contenido_html = ""
        if e.get("content"):
            contenido_html = e.content[0].get("value", "")
        entradas.append(Entrada(
            titulo=e.get("title", "") or "",
            link=e.get("link", "") or "",
            resumen=e.get("summary", "") or "",
            contenido=contenido_html,
            fecha=_fecha_struct(e.get("published_parsed") or e.get("updated_parsed")),
        ))
    return entradas


def _local(tag):
    return tag.rsplit("}", 1)[-1] if "}" in tag else tag


def _hijo(nodo, nombre):
    for h in nodo:
        if _local(h.tag) == nombre:
            return h
    return None


def _texto(nodo, nombre):
    h = _hijo(nodo, nombre)
    return (h.text or "").strip() if h is not None else ""


def _fecha_texto(valor):
    if not valor:
        return None
    try:
        dt = parsedate_to_datetime(valor)  # RFC 822 (RSS)
    except (TypeError, ValueError):
        try:
            dt = datetime.fromisoformat(valor.replace("Z", "+00:00"))  # ISO (Atom)
        except ValueError:
            return None
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    return dt.astimezone(timezone.utc)


def _parsear_basico(contenido):
    """Parser minimo RSS 2.0 / Atom. Respaldo si falta feedparser."""
    try:
        raiz = ET.fromstring(contenido)
    except ET.ParseError as e:
        raise ErrorFeed(f"XML invalido: {e}") from None

    entradas = []
    for nodo in raiz.iter():
        nombre = _local(nodo.tag)
        if nombre == "item":  # RSS
            entradas.append(Entrada(
                titulo=_texto(nodo, "title"),
                link=_texto(nodo, "link"),
                resumen=_texto(nodo, "description"),
                contenido=_texto(nodo, "encoded"),
                fecha=_fecha_texto(_texto(nodo, "pubDate") or _texto(nodo, "date")),
            ))
        elif nombre == "entry":  # Atom
            link = ""
            for h in nodo:
                if _local(h.tag) == "link" and h.get("rel", "alternate") == "alternate":
                    link = h.get("href", "")
                    break
            entradas.append(Entrada(
                titulo=_texto(nodo, "title"),
                link=link,
                resumen=_texto(nodo, "summary"),
                contenido=_texto(nodo, "content"),
                fecha=_fecha_texto(_texto(nodo, "published") or _texto(nodo, "updated")),
            ))
    return entradas


# ---------------------------------------------------------------------------
# Articulo completo (solo para fuentes que lo necesitan, p. ej. Young Guitar)
# ---------------------------------------------------------------------------

_SELECTORES_CUERPO = [
    "article .entry-content", ".entry-content", ".post-content",
    "article .content", "article", "main",
]


def extraer_articulo(url, timeout=12, maximo=5000):
    """Texto del cuerpo del articulo, priorizando el contenedor principal
    para no arrastrar navegacion, relacionados ni avisos de cookies."""
    try:
        r = requests.get(url, headers=HEADERS_HTTP, timeout=timeout)
        r.raise_for_status()
    except requests.exceptions.RequestException as e:
        log.warning(f"No se pudo leer el articulo ({type(e).__name__}): {url}")
        return ""

    soup = BeautifulSoup(r.text, "html.parser")
    for tag in soup(["script", "style", "nav", "footer", "header", "aside", "form"]):
        tag.decompose()

    cuerpo = None
    for selector in _SELECTORES_CUERPO:
        cuerpo = soup.select_one(selector)
        if cuerpo:
            break
    cuerpo = cuerpo or soup

    parrafos = [p.get_text(" ", strip=True) for p in cuerpo.find_all("p")]
    parrafos = [t for t in parrafos if len(t) >= 25]
    return " ".join(parrafos)[:maximo]


# =============================================================================
# clasificador
#   Clasificacion de entradas: instrumento, tipo de noticia, segmento y marcas.
#
#   Todas las coincidencias usan limites de palabra (no subcadenas), sobre texto
#   en minusculas y sin acentos. Asi 'amp' no coincide con 'example', 'bass' no
#   coincide con 'ambassador' y 'drum' no coincide con 'eardrum'.
# =============================================================================

def compilar_lista(palabras, plural=True):
    """Regex con limites de palabra para una lista de terminos.

    Los espacios del termino aceptan espacio o guion ('amp sim' = 'amp-sim').
    Con plural=True acepta 's'/'es' finales ('cymbal' -> 'cymbals').
    Los terminos largos van primero para que ganen a los cortos.
    """
    terminos = sorted({sin_acentos(p).strip() for p in palabras if p and p.strip()},
                      key=len, reverse=True)
    if not terminos:
        return None
    partes = []
    for t in terminos:
        cuerpo = re.escape(t).replace(r"\ ", r"[\s\-]+")
        # Limites solo en los extremos que son caracteres de palabra:
        # asi funcionan terminos como '% off' o 'd&b'.
        inicio = r"(?<!\w)" if (t[0].isalnum() or t[0] == "_") else ""
        if t[-1].isalnum() or t[-1] == "_":
            fin = (r"(?:e?s)?" if plural else "") + r"(?!\w)"
        else:
            fin = ""
        partes.append(f"{inicio}(?:{cuerpo}){fin}")
    # Cada termino es un grupo con nombre: m.lastgroup identifica el termino
    # (sin importar el plural) para contar coincidencias distintas.
    return re.compile("|".join(f"(?P<t{i}>{p})" for i, p in enumerate(partes)))


def _coincidencias(regex, texto):
    if regex is None or not texto:
        return set()
    return {m.lastgroup for m in regex.finditer(texto)}


@dataclass
class Clasificacion:
    instrumento: str
    puntos: dict
    tipo: str            # lanzamiento | otro
    segmento: str = ""
    marcas: list = field(default_factory=list)


class Clasificador:
    PESO_TITULO = 3
    PESO_RESUMEN = 1

    def __init__(self, cfg):
        self.instrumentos = {}
        for clave, icfg in cfg["instrumentos"].items():
            self.instrumentos[clave] = {
                "clave": compilar_lista(icfg.get("palabras_clave", [])),
                "excl": compilar_lista(icfg.get("exclusiones", [])),
                "filtrar_ruido": bool(icfg.get("filtrar_ruido", False)),
                "segmentos": [
                    (etiqueta, compilar_lista(kws))
                    for etiqueta, kws in (icfg.get("segmentos") or {}).items()
                ],
            }

        ccfg = cfg.get("clasificacion", {})
        self.re_ruido = compilar_lista(ccfg.get("patrones_ruido", []), plural=False)
        self.re_lanzamiento = compilar_lista(ccfg.get("patrones_lanzamiento", []), plural=False)
        self.re_oferta = compilar_lista(ccfg.get("patrones_oferta", []), plural=False)
        self.excluir_ofertas = bool(ccfg.get("excluir_ofertas", True))

        self.marcas = []
        for marca in cfg.get("marcas", []):
            regex = compilar_lista([marca], plural=False)
            etiqueta = hashtag(marca)
            if regex and etiqueta:
                self.marcas.append((etiqueta, regex))

    # ------------------------------------------------------------------

    def puntuar(self, instrumento, titulo_n, resumen_n):
        datos = self.instrumentos[instrumento]
        en_titulo = _coincidencias(datos["clave"], titulo_n)
        en_resumen = _coincidencias(datos["clave"], resumen_n) - en_titulo
        return self.PESO_TITULO * len(en_titulo) + self.PESO_RESUMEN * len(en_resumen)

    def excluido(self, instrumento, titulo_n):
        return bool(_coincidencias(self.instrumentos[instrumento]["excl"], titulo_n))

    def tipo(self, titulo_n):
        if _coincidencias(self.re_ruido, titulo_n):
            return "ruido"
        if _coincidencias(self.re_lanzamiento, titulo_n):
            return "lanzamiento"
        return "otro"

    def clasificar(self, titulo, resumen, fuente):
        """Devuelve Clasificacion o None si la entrada no es relevante.

        - Fuente especializada con un solo instrumento: se acepta sin mirar
          palabras clave ni exclusiones (confiamos en la fuente).
        - Resto: se puntua cada instrumento declarado por la fuente; las
          exclusiones (en el titulo) anulan ese instrumento. Gana el de mayor
          puntuacion; en empate, el primero que declara la fuente.
        """
        titulo_n = sin_acentos(titulo)
        resumen_n = sin_acentos(resumen)
        candidatos = [i for i in fuente["instrumentos"] if i in self.instrumentos]
        if not candidatos:
            return None

        if fuente.get("especializada") and len(candidatos) == 1:
            instrumento = candidatos[0]
            puntos = {instrumento: max(1, self.puntuar(instrumento, titulo_n, resumen_n))}
        else:
            puntos = {}
            for inst in candidatos:
                if self.excluido(inst, titulo_n):
                    continue
                p = self.puntuar(inst, titulo_n, resumen_n)
                if p > 0:
                    puntos[inst] = p
            if not puntos:
                return None
            instrumento = max(candidatos, key=lambda i: (puntos.get(i, 0), -candidatos.index(i)))

        if self.excluir_ofertas and _coincidencias(self.re_oferta, titulo_n):
            return None

        tipo = self.tipo(titulo_n)
        if tipo == "ruido" and self.instrumentos[instrumento]["filtrar_ruido"]:
            return None
        if tipo == "ruido":
            tipo = "otro"

        texto = f"{titulo_n} {resumen_n}"
        segmento = ""
        mejor = 0
        for etiqueta, regex in self.instrumentos[instrumento]["segmentos"]:
            n = len(_coincidencias(regex, texto))
            if n > mejor:
                segmento, mejor = etiqueta, n

        marcas = [et for et, regex in self.marcas if regex.search(texto)][:3]

        return Clasificacion(instrumento=instrumento, puntos=puntos, tipo=tipo,
                             segmento=segmento, marcas=marcas)


# =============================================================================
# db
#   Persistencia en SQLite: pool de noticias, grupos de duplicados, historial
#   de publicadas y estado de las fuentes.
#
#   Capas que garantizan que una noticia no se repite:
#     1. `historial.url_norm`  - URL normalizada de todo lo publicado (y de los
#                                duplicados que llegaron despues).
#     2. `historial.tokens`    - titulo de lo publicado: la misma historia de otra
#                                fuente con otra URL tampoco se publica.
#     3. `grupos.estado`       - un grupo publicado no vuelve a salir aunque se le
#                                sumen fuentes nuevas.
#     4. `items.url_norm` UNIQUE - una URL entra al pool una sola vez.
# =============================================================================

ESQUEMA = """
CREATE TABLE IF NOT EXISTS grupos (
    id              INTEGER PRIMARY KEY,
    tokens          TEXT NOT NULL,
    instrumento     TEXT NOT NULL,
    tipo            TEXT NOT NULL DEFAULT 'otro',
    creado_en       TEXT NOT NULL,
    actualizado_en  TEXT NOT NULL,
    estado          TEXT NOT NULL DEFAULT 'pendiente',
    intentos        INTEGER NOT NULL DEFAULT 0,
    ultimo_error    TEXT,
    publicado_en    TEXT,
    destino         TEXT,
    message_id      INTEGER,
    titulo_publicado TEXT,
    fuente_publicada TEXT
);
CREATE INDEX IF NOT EXISTS ix_grupos_estado ON grupos(estado, instrumento);
CREATE INDEX IF NOT EXISTS ix_grupos_creado ON grupos(creado_en);

CREATE TABLE IF NOT EXISTS items (
    id              INTEGER PRIMARY KEY,
    grupo_id        INTEGER NOT NULL REFERENCES grupos(id) ON DELETE CASCADE,
    url_norm        TEXT NOT NULL UNIQUE,
    url             TEXT NOT NULL,
    fuente          TEXT NOT NULL,
    editorial       TEXT,
    idioma          TEXT NOT NULL,
    titulo          TEXT NOT NULL,
    resumen         TEXT NOT NULL DEFAULT '',
    extraer_articulo INTEGER NOT NULL DEFAULT 0,
    puntos          TEXT NOT NULL DEFAULT '{}',
    segmento        TEXT NOT NULL DEFAULT '',
    marcas          TEXT NOT NULL DEFAULT '[]',
    fecha_feed      TEXT,
    detectado_en    TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS ix_items_grupo ON items(grupo_id);

CREATE TABLE IF NOT EXISTS historial (
    url_norm        TEXT PRIMARY KEY,
    tokens          TEXT NOT NULL DEFAULT '',
    motivo          TEXT NOT NULL DEFAULT 'publicada',
    registrado_en   TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS ix_historial_fecha ON historial(registrado_en);

CREATE TABLE IF NOT EXISTS fuentes_estado (
    nombre              TEXT PRIMARY KEY,
    ultimo_ok           TEXT,
    ultimo_error        TEXT,
    ultimo_error_en     TEXT,
    entradas            INTEGER NOT NULL DEFAULT 0,
    fallos_consecutivos INTEGER NOT NULL DEFAULT 0
);

CREATE TABLE IF NOT EXISTS ejecuciones (
    id      INTEGER PRIMARY KEY,
    ts      TEXT NOT NULL,
    tipo    TEXT NOT NULL,
    datos   TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS marcas_envio (
    clave   TEXT PRIMARY KEY,
    ts      TEXT NOT NULL
);
"""


def iso(dt):
    return dt.astimezone(timezone.utc).isoformat(timespec="seconds")


def desde_iso(texto):
    return datetime.fromisoformat(texto) if texto else None


class BaseDatos:
    def __init__(self, ruta):
        # journal_mode DELETE (por defecto): un solo archivo, comodo para
        # versionarlo en git desde GitHub Actions.
        self.con = sqlite3.connect(ruta)
        self.con.row_factory = sqlite3.Row
        self.con.execute("PRAGMA foreign_keys = ON")
        self.con.executescript(ESQUEMA)
        self.con.commit()

    @classmethod
    def copia_en_memoria(cls, ruta):
        """Para --dry-run: trabaja sobre una copia en memoria, de modo que
        la simulacion no marque nada como publicado en el archivo real."""
        origen = cls(ruta)
        copia = cls(":memory:")
        origen.con.backup(copia.con)
        origen.con.close()
        return copia

    def cerrar(self):
        self.con.commit()
        self.con.close()

    def commit(self):
        self.con.commit()

    # ------------------------------------------------------------------
    # Historial
    # ------------------------------------------------------------------

    def url_conocida(self, url_norm):
        """True si la URL ya fue publicada/registrada o ya esta en el pool."""
        c = self.con.execute(
            "SELECT 1 FROM historial WHERE url_norm=? UNION ALL "
            "SELECT 1 FROM items WHERE url_norm=? LIMIT 1", (url_norm, url_norm))
        return c.fetchone() is not None

    def registrar_historial(self, url_norm, tokens, motivo, ahora):
        self.con.execute(
            "INSERT OR IGNORE INTO historial(url_norm, tokens, motivo, registrado_en) "
            "VALUES (?,?,?,?)", (url_norm, tokens, motivo, iso(ahora)))

    def urls_historial(self, limite=5000):
        c = self.con.execute(
            "SELECT url_norm FROM historial WHERE motivo IN ('publicada','migrada','duplicado') "
            "ORDER BY registrado_en DESC, url_norm LIMIT ?", (limite,))
        return [r["url_norm"] for r in c]

    def titulos_publicados_desde(self, desde):
        c = self.con.execute(
            "SELECT tokens FROM historial WHERE motivo='publicada' AND tokens<>'' "
            "AND registrado_en>=?", (iso(desde),))
        return [r["tokens"] for r in c]

    # ------------------------------------------------------------------
    # Grupos e items
    # ------------------------------------------------------------------

    def grupos_desde(self, desde):
        c = self.con.execute(
            "SELECT id, tokens, estado FROM grupos WHERE creado_en>=?", (iso(desde),))
        return [dict(r) for r in c]

    def crear_grupo(self, tokens, instrumento, tipo, ahora):
        c = self.con.execute(
            "INSERT INTO grupos(tokens, instrumento, tipo, creado_en, actualizado_en) "
            "VALUES (?,?,?,?,?)", (tokens, instrumento, tipo, iso(ahora), iso(ahora)))
        return c.lastrowid

    def anadir_item(self, grupo_id, item, ahora):
        self.con.execute(
            "INSERT OR IGNORE INTO items(grupo_id, url_norm, url, fuente, editorial, idioma, "
            "titulo, resumen, extraer_articulo, puntos, segmento, marcas, fecha_feed, detectado_en) "
            "VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
            (grupo_id, item["url_norm"], item["url"], item["fuente"], item.get("editorial"),
             item["idioma"], item["titulo"], item.get("resumen", ""),
             int(bool(item.get("extraer_articulo"))), json.dumps(item.get("puntos", {})),
             item.get("segmento", ""), json.dumps(item.get("marcas", [])),
             item.get("fecha_feed"), iso(ahora)))
        self._recalcular_grupo(grupo_id, ahora)

    def _recalcular_grupo(self, grupo_id, ahora):
        """Instrumento del grupo = suma de puntos de todos sus items.
        Tipo = 'lanzamiento' si alguno lo es."""
        items = self.items_de_grupo(grupo_id)
        if not items:
            return
        totales = {}
        for it in items:
            for inst, p in json.loads(it["puntos"]).items():
                totales[inst] = totales.get(inst, 0) + p
        instrumento = max(totales, key=totales.get) if totales else None
        sets = ["actualizado_en=?"]
        params = [iso(ahora)]
        if instrumento:
            sets.append("instrumento=?")
            params.append(instrumento)
        params.append(grupo_id)
        self.con.execute(f"UPDATE grupos SET {', '.join(sets)} WHERE id=?", params)

    def marcar_tipo(self, grupo_id, tipo):
        if tipo == "lanzamiento":
            self.con.execute("UPDATE grupos SET tipo='lanzamiento' WHERE id=?", (grupo_id,))

    def grupo(self, grupo_id):
        r = self.con.execute("SELECT * FROM grupos WHERE id=?", (grupo_id,)).fetchone()
        return dict(r) if r else None

    def items_de_grupo(self, grupo_id):
        c = self.con.execute("SELECT * FROM items WHERE grupo_id=? ORDER BY id", (grupo_id,))
        return [dict(r) for r in c]

    def n_fuentes(self, grupo_id):
        """Fuentes distintas; medios de la misma editorial cuentan una vez."""
        r = self.con.execute(
            "SELECT COUNT(DISTINCT COALESCE(editorial, fuente)) AS n FROM items WHERE grupo_id=?",
            (grupo_id,)).fetchone()
        return r["n"]

    def pendientes(self, desde, instrumento=None):
        sql = "SELECT * FROM grupos WHERE estado='pendiente' AND creado_en>=?"
        params = [iso(desde)]
        if instrumento:
            sql += " AND instrumento=?"
            params.append(instrumento)
        return [dict(r) for r in self.con.execute(sql, params)]

    def marcar_publicada(self, grupo_id, destino, message_id, ahora, titulo="", fuente=""):
        self.con.execute(
            "UPDATE grupos SET estado='publicada', publicado_en=?, destino=?, message_id=?, "
            "titulo_publicado=?, fuente_publicada=? WHERE id=?",
            (iso(ahora), destino, message_id, titulo, fuente, grupo_id))
        tokens = self.grupo(grupo_id)["tokens"]
        for it in self.items_de_grupo(grupo_id):
            self.registrar_historial(it["url_norm"], tokens, "publicada", ahora)
        self.con.commit()  # cada publicacion se persiste al momento

    def marcar_fallo(self, grupo_id, motivo, max_intentos):
        self.con.execute(
            "UPDATE grupos SET intentos=intentos+1, ultimo_error=? WHERE id=?",
            (motivo[:300], grupo_id))
        g = self.grupo(grupo_id)
        if g["intentos"] >= max_intentos:
            self.con.execute("UPDATE grupos SET estado='descartada' WHERE id=?", (grupo_id,))
            self.con.commit()
            return True
        self.con.commit()
        return False

    def marcar_descartada(self, grupo_id, motivo):
        self.con.execute(
            "UPDATE grupos SET estado='descartada', ultimo_error=? WHERE id=?",
            (motivo[:300], grupo_id))
        self.con.commit()

    def publicadas_desde(self, desde, destino=None):
        sql = "SELECT * FROM grupos WHERE estado='publicada' AND publicado_en>=?"
        params = [iso(desde)]
        if destino:
            sql += " AND destino=?"
            params.append(destino)
        return [dict(r) for r in self.con.execute(sql + " ORDER BY publicado_en", params)]

    def resumen_pool(self, desde):
        c = self.con.execute(
            "SELECT instrumento, COUNT(*) AS n FROM grupos WHERE estado='pendiente' "
            "AND creado_en>=? GROUP BY instrumento", (iso(desde),))
        return {r["instrumento"]: r["n"] for r in c}

    # ------------------------------------------------------------------
    # Mantenimiento
    # ------------------------------------------------------------------

    def purgar(self, ahora, dias_pool, dias_historial):
        """Caduca pendientes viejas y borra grupos cerrados antiguos.
        El historial de URLs se conserva mucho mas tiempo que el pool."""
        limite_pool = iso(ahora - timedelta(days=dias_pool))
        self.con.execute(
            "UPDATE grupos SET estado='caducada' WHERE estado='pendiente' AND creado_en<?",
            (limite_pool,))
        limite_borrado = iso(ahora - timedelta(days=dias_pool * 3))
        # Antes de borrar items de grupos no publicados, su URL pasa al
        # historial: asi no reingresan al pool si siguen en el feed.
        c = self.con.execute(
            "SELECT i.url_norm, g.tokens, g.estado FROM items i JOIN grupos g ON g.id=i.grupo_id "
            "WHERE g.estado IN ('caducada','descartada') AND g.creado_en<?", (limite_borrado,))
        for r in c.fetchall():
            self.registrar_historial(r["url_norm"], "", r["estado"], ahora)
        self.con.execute(
            "DELETE FROM grupos WHERE estado<>'pendiente' AND creado_en<?", (limite_borrado,))
        self.con.execute(
            "DELETE FROM historial WHERE registrado_en<?",
            (iso(ahora - timedelta(days=dias_historial)),))
        self.con.commit()

    # ------------------------------------------------------------------
    # Fuentes y ejecuciones
    # ------------------------------------------------------------------

    def fuente_ok(self, nombre, entradas, ahora):
        self.con.execute(
            "INSERT INTO fuentes_estado(nombre, ultimo_ok, entradas, fallos_consecutivos) "
            "VALUES (?,?,?,0) ON CONFLICT(nombre) DO UPDATE SET ultimo_ok=excluded.ultimo_ok, "
            "entradas=excluded.entradas, fallos_consecutivos=0",
            (nombre, iso(ahora), entradas))

    def fuente_error(self, nombre, error, ahora):
        self.con.execute(
            "INSERT INTO fuentes_estado(nombre, ultimo_error, ultimo_error_en, entradas, "
            "fallos_consecutivos) VALUES (?,?,?,0,1) ON CONFLICT(nombre) DO UPDATE SET "
            "ultimo_error=excluded.ultimo_error, ultimo_error_en=excluded.ultimo_error_en, "
            "entradas=0, fallos_consecutivos=fuentes_estado.fallos_consecutivos+1",
            (nombre, error, iso(ahora)))

    def fuentes_con_problemas(self, minimo=1):
        c = self.con.execute(
            "SELECT * FROM fuentes_estado WHERE fallos_consecutivos>=? ORDER BY nombre",
            (minimo,))
        return [dict(r) for r in c]

    def registrar_ejecucion(self, tipo, datos, ahora):
        self.con.execute("INSERT INTO ejecuciones(ts, tipo, datos) VALUES (?,?,?)",
                         (iso(ahora), tipo, json.dumps(datos, ensure_ascii=False)))
        self.con.commit()

    def envio_hecho(self, clave):
        return self.con.execute(
            "SELECT 1 FROM marcas_envio WHERE clave=?", (clave,)).fetchone() is not None

    def marcar_envio(self, clave, ahora):
        self.con.execute("INSERT OR IGNORE INTO marcas_envio(clave, ts) VALUES (?,?)",
                         (clave, iso(ahora)))
        self.con.commit()


# =============================================================================
# mensajes
#   Plantillas de mensajes (HTML de Telegram). Todo texto externo se escapa.
# =============================================================================

NOMBRE_DIAS = ["lunes", "martes", "miercoles", "jueves", "viernes", "sabado", "domingo"]


def mensaje_noticia(item, titulo_es, resumen_es, instrumento_cfg, cfg,
                    destacada=False, n_fuentes=1, expandible=True):
    pcfg = cfg.get("publicacion", {})
    visible = pcfg.get("largo_resumen_visible", 300)

    contexto = [f"{instrumento_cfg.get('emoji', '')} <b>{escape(instrumento_cfg['nombre'].upper())}</b>".strip()]
    if item.get("segmento"):
        contexto.append(escape(item["segmento"]))
    contexto.append(escape(item["fuente"]))
    lineas = []
    if destacada:
        lineas.append(f"⭐ <b>DESTACADA</b> · cubierta por {n_fuentes} fuentes")
    lineas.append(" · ".join(contexto))
    lineas.append(f"<b>{escape(titulo_es)}</b>")

    if resumen_es:
        lineas.append("")
        if expandible and len(resumen_es) > visible:
            lineas.append(f"<blockquote expandable>{escape(resumen_es)}</blockquote>")
        else:
            lineas.append(escape(truncar(resumen_es, visible)))

    etiquetas = [instrumento_cfg.get("hashtag") or hashtag(instrumento_cfg["nombre"])]
    if item.get("segmento"):
        etiquetas.append(hashtag(item["segmento"]))
    etiquetas.extend(item.get("marcas") or [])
    etiquetas = [e for e in dict.fromkeys(etiquetas) if e]
    lineas.append("")
    if etiquetas:
        lineas.append(" ".join(f"#{e}" for e in etiquetas))
    lineas.append(f'🔗 <a href="{escape(item["url"])}">Leer artículo</a>')
    return "\n".join(lineas)


def mensaje_estado(ahora_local, datos):
    l = [f"📊 <b>Ejecución {ahora_local.strftime('%d/%m %H:%M')}</b> ({escape(datos.get('dia', ''))})"]
    if "recoleccion" in datos:
        r = datos["recoleccion"]
        l.append(f"Recolección: {r['nuevas']} nuevas · {r['agrupadas']} agrupadas · "
                 f"{r['duplicadas_publicadas']} ya publicadas · feeds OK {r['fuentes_ok']}"
                 f"/{r['fuentes_ok'] + r['fuentes_error']}")
    if "publicacion" in datos:
        p = datos["publicacion"]
        partes = [f"{escape(k)} {v['publicadas']}/{v['cupo']}" for k, v in p["por_destino"].items()]
        l.append("Publicadas: " + (" · ".join(partes) if partes else "ninguna"))
        l.append(f"Descartadas por traducción: {p['descartadas_traduccion']} · "
                 f"fallos de envío: {p['fallos_envio']}")
        if p.get("breaker"):
            l.append(f"⚠️ Circuit breaker: {escape(p['breaker'])}")
    l.append(f"Traductor: {escape(datos.get('proveedor') or 'NO DISPONIBLE (solo español)')}")
    pool = datos.get("pool") or {}
    if pool:
        l.append("Pool pendiente: " + " · ".join(f"{escape(k)} {v}" for k, v in sorted(pool.items())))
    problemas = datos.get("fuentes_problemas") or []
    if problemas:
        l.append("⚠️ Feeds con problemas: " + ", ".join(
            f"{escape(f['nombre'])} ({escape(f['ultimo_error'] or '?')}, x{f['fallos_consecutivos']})"
            for f in problemas[:12]))
    return "\n".join(l)


def mensaje_indice(titulo, filas):
    """filas: lista de (emoji_instrumento, titulo, enlace o None)."""
    l = [f"📰 <b>{escape(titulo)}</b>", ""]
    for emoji, texto, enlace in filas:
        if enlace:
            l.append(f'{emoji} <a href="{escape(enlace)}">{escape(truncar(texto, 90))}</a>')
        else:
            l.append(f"{emoji} {escape(truncar(texto, 90))}")
    return "\n".join(l)


def nombre_dia(fecha_local: datetime):
    return NOMBRE_DIAS[fecha_local.weekday()]


# =============================================================================
# config
#   Carga y validacion de config.yaml. Falla pronto y con mensajes claros:
#   un error de configuracion no debe descubrirse a mitad de una publicacion.
# =============================================================================

try:
    import yaml
except ImportError:  # solo hace falta para leer config.yaml externo
    yaml = None


IDIOMAS = {"es", "en", "ja"}


class ErrorConfig(Exception):
    pass


def cargar(ruta, por_defecto=None):
    """Lee `ruta` (YAML). Si no existe y hay configuracion integrada
    (`por_defecto`), usa esa: asi telegram_bot.py funciona sin config.yaml."""
    if not os.path.exists(ruta) and por_defecto is not None:
        cfg = copy.deepcopy(por_defecto)
    else:
        if yaml is None:
            raise ErrorConfig("Para leer config.yaml instala PyYAML: pip install pyyaml")
        with open(ruta, encoding="utf-8") as f:
            cfg = yaml.safe_load(f) or {}
    validar(cfg)
    return cfg


def validar(cfg):
    errores = []
    for seccion in ("general", "telegram", "agrupacion", "traduccion", "publicacion",
                    "instrumentos", "fuentes"):
        if seccion not in cfg:
            errores.append(f"falta la seccion '{seccion}'")
    if errores:
        raise ErrorConfig("; ".join(errores))

    instrumentos = cfg["instrumentos"]
    for clave, icfg in instrumentos.items():
        if "nombre" not in icfg:
            errores.append(f"instrumento '{clave}': falta 'nombre'")

    nombres = set()
    for i, f in enumerate(cfg["fuentes"]):
        ref = f.get("nombre", f"#{i}")
        for campo in ("nombre", "url", "instrumentos"):
            if campo not in f:
                errores.append(f"fuente {ref}: falta '{campo}'")
        if f.get("nombre") in nombres:
            errores.append(f"fuente duplicada: {ref}")
        nombres.add(f.get("nombre"))
        for inst in f.get("instrumentos", []):
            if inst not in instrumentos:
                errores.append(f"fuente {ref}: instrumento desconocido '{inst}'")
        if f.get("idioma", "en") not in IDIOMAS:
            errores.append(f"fuente {ref}: idioma '{f.get('idioma')}' no soportado {sorted(IDIOMAS)}")

    calendario = cfg["publicacion"].get("calendario") or {}
    for dia, plan in calendario.items():
        if dia not in NOMBRE_DIAS:
            errores.append(f"calendario: dia '{dia}' invalido (usa {NOMBRE_DIAS})")
        for inst, cupo in (plan or {}).items():
            if inst not in instrumentos:
                errores.append(f"calendario {dia}: instrumento desconocido '{inst}'")
            if not isinstance(cupo, int) or cupo < 0:
                errores.append(f"calendario {dia}/{inst}: cupo debe ser entero >= 0")

    temas = cfg["telegram"].get("temas") or {}
    destinos_validos = set(instrumentos) | {"destacadas", "estado"}
    for destino in temas:
        if destino not in destinos_validos:
            errores.append(f"telegram.temas: destino desconocido '{destino}'")

    if errores:
        raise ErrorConfig("Configuracion invalida:\n  - " + "\n  - ".join(errores))


# =============================================================================
# recoleccion
#   Recoleccion: lee todos los feeds, filtra, clasifica, agrupa duplicados y
#   guarda en el pool. No traduce ni publica nada.
#
#   Se recomienda ejecutarla varias veces al dia: los feeds solo muestran sus
#   ultimas 10-20 entradas y una fuente con mucho volumen puede 'perder' noticias
#   si se lee una vez por semana.
# =============================================================================

log = logging.getLogger("gear_news.recoleccion")


class Agrupador:
    """Asigna cada titulo nuevo a un grupo existente (misma noticia) o None."""

    def __init__(self, grupos, cfg_agr):
        self.grupos = [(g["id"], deserializar_tokens(g["tokens"])) for g in grupos]
        self.kw = dict(
            umbral_jaccard=cfg_agr.get("umbral_jaccard", 0.7),
            umbral_solapamiento=cfg_agr.get("umbral_solapamiento", 0.8),
            min_comunes=cfg_agr.get("min_tokens_comunes", 3),
        )

    def buscar(self, tokens):
        mejor, mejor_comunes = None, 0
        for gid, gtokens in self.grupos:
            if titulos_similares(tokens, gtokens, **self.kw):
                comunes = len(tokens & gtokens)
                if comunes > mejor_comunes:
                    mejor, mejor_comunes = gid, comunes
        return mejor

    def anadir(self, gid, tokens):
        self.grupos.append((gid, tokens))

    def similar_a_alguno(self, tokens, lista_tokens):
        return any(titulos_similares(tokens, t, **self.kw) for t in lista_tokens)


def recolectar(cfg, db, clasificador, ahora, leer_fuente=None, pausa=None):
    """Devuelve estadisticas de la recoleccion."""
    leer_fuente = leer_fuente or feeds_mod.leer_fuente
    g = cfg["general"]
    pausa = g.get("pausa_entre_feeds", 1) if pausa is None else pausa
    limite_fecha = ahora - timedelta(days=g.get("antiguedad_max_entrada_dias", 10))
    max_entradas = g.get("max_entradas_por_feed", 25)
    tr = cfg.get("traduccion", {})
    max_titulo = tr.get("max_largo_titulo", 250)

    agrupador = Agrupador(
        db.grupos_desde(ahora - timedelta(hours=cfg["agrupacion"].get("ventana_horas", 72))),
        cfg["agrupacion"])
    publicados = [deserializar_tokens(t) for t in db.titulos_publicados_desde(
        ahora - timedelta(days=g.get("dias_historial_titulos", 45)))]

    stats = {"fuentes_ok": 0, "fuentes_error": 0, "nuevas": 0, "agrupadas": 0,
             "duplicadas_publicadas": 0, "irrelevantes": 0, "antiguas": 0}

    for fuente in cfg["fuentes"]:
        if not fuente.get("activa", True):
            continue
        entradas, error = leer_fuente(fuente["url"], g.get("timeout_http", 15))
        if error:
            db.fuente_error(fuente["nombre"], error, ahora)
            stats["fuentes_error"] += 1
            log.warning(f"[{fuente['nombre']}] {error}")
            continue
        db.fuente_ok(fuente["nombre"], len(entradas), ahora)
        stats["fuentes_ok"] += 1

        nuevas_fuente = 0
        for e in entradas[:max_entradas]:
            titulo = truncar(limpiar_html(e.titulo), max_titulo, sufijo="")
            if not titulo or not e.link:
                continue
            if e.fecha and e.fecha < limite_fecha:
                stats["antiguas"] += 1
                continue
            url_norm = normalizar_url(e.link)
            if db.url_conocida(url_norm):
                continue

            # El contenido completo (content:encoded) suele ser mejor que el
            # extracto, sobre todo en fuentes japonesas.
            resumen = limpiar_resumen(e.contenido) or limpiar_resumen(e.resumen)

            clas = clasificador.clasificar(titulo, resumen, fuente)
            if clas is None:
                stats["irrelevantes"] += 1
                continue

            tokens = tokens_titulo(titulo)
            tokens_txt = serializar_tokens(tokens)

            # Misma historia ya publicada desde otra fuente/URL -> no repetir.
            if agrupador.similar_a_alguno(tokens, publicados):
                db.registrar_historial(url_norm, tokens_txt, "duplicado", ahora)
                stats["duplicadas_publicadas"] += 1
                continue

            item = {
                "url_norm": url_norm, "url": e.link.strip(), "fuente": fuente["nombre"],
                "editorial": fuente.get("editorial"), "idioma": fuente.get("idioma", "en"),
                "titulo": titulo, "resumen": resumen,
                "extraer_articulo": fuente.get("extraer_articulo", False),
                "puntos": clas.puntos, "segmento": clas.segmento, "marcas": clas.marcas,
                "fecha_feed": iso(e.fecha) if e.fecha else None,
            }

            gid = agrupador.buscar(tokens)
            if gid is not None:
                db.anadir_item(gid, item, ahora)
                db.marcar_tipo(gid, clas.tipo)
                grupo = db.grupo(gid)
                if grupo["estado"] == "publicada":
                    # Llega tarde una fuente nueva de algo ya publicado.
                    db.registrar_historial(url_norm, grupo["tokens"], "publicada", ahora)
                    stats["duplicadas_publicadas"] += 1
                else:
                    stats["agrupadas"] += 1
            else:
                gid = db.crear_grupo(tokens_txt, clas.instrumento, clas.tipo, ahora)
                db.anadir_item(gid, item, ahora)
                agrupador.anadir(gid, tokens)
                stats["nuevas"] += 1
            nuevas_fuente += 1

        db.commit()
        log.info(f"[{fuente['nombre']}] {len(entradas)} entradas, {nuevas_fuente} al pool")
        if pausa:
            time.sleep(pausa)

    db.purgar(ahora, g.get("dias_en_pool", 10), g.get("dias_historial_urls", 365))
    return stats


# =============================================================================
# traduccion
#   Adaptador sobre traductor.py (tu modulo multi-proveedor con cache).
#
#   Interfaz esperada de traductor.py (la misma que usan tus bots actuales):
#       traducir_estricto(texto, origen=..., validador=...) -> str
#       TraduccionFallida (Exception)
#       autotest() -> nombre del proveedor o None
#       proveedores_agotados() -> bool
#       resumen_stats() -> str
#       guardar_cache() -> None
# =============================================================================

log = logging.getLogger("gear_news.traduccion")


class FalloTraduccion(Exception):
    pass


_PALABRAS_INGLES = set(
    "the and with for from this that new its are is was will has have of to in on "
    "your our their how why what into about after".split())


def validador_no_identica(original):
    """Rechaza una 'traduccion' que es el texto original en ingles.

    Un titulo formado solo por nombres propios ('Neural DSP Quad Cortex Mini')
    puede quedar igual legitimamente, por eso solo se rechaza si el texto
    tiene palabras funcionales del ingles.
    """
    base = " ".join(sin_acentos(original).split())
    tiene_ingles = len(set(base.split()) & _PALABRAS_INGLES) >= 2

    def validar(traducido):
        if not traducido or not traducido.strip():
            return False
        if tiene_ingles and " ".join(sin_acentos(traducido).split()) == base:
            return False
        return True
    return validar


def validador_sin_japones(texto):
    return bool(texto) and not contiene_japones(texto)


class Traductor:
    def __init__(self, cfg, modulo=None, extraer_articulo=None):
        self.cfg = cfg.get("traduccion", {})
        self.mod = modulo
        self.proveedor = None
        self._extraer_articulo = extraer_articulo

    # ------------------------------------------------------------------

    def iniciar(self):
        """Carga traductor.py y ejecuta su autotest. Devuelve True si hay
        traductor disponible. Sin traductor el bot sigue funcionando en modo
        'solo espanol' (publica solo fuentes que no necesitan traduccion)."""
        if self.mod is None:
            try:
                self.mod = importlib.import_module("traductor")
            except ImportError:
                log.error("No se encontro traductor.py: modo solo espanol.")
                return False
        try:
            self.proveedor = self.mod.autotest()
        except Exception:
            log.exception("autotest() del traductor fallo")
            self.proveedor = None
        if self.proveedor is None:
            log.error("Autotest sin proveedor disponible: modo solo espanol.")
        return self.proveedor is not None

    @property
    def disponible(self):
        return self.mod is not None and self.proveedor is not None

    def agotado(self):
        try:
            return bool(self.mod.proveedores_agotados())
        except Exception:
            return False

    def cerrar(self):
        if self.mod is None:
            return ""
        try:
            self.mod.guardar_cache()
        except Exception:
            log.exception("guardar_cache() fallo")
        try:
            return self.mod.resumen_stats()
        except Exception:
            return ""

    # ------------------------------------------------------------------

    def _traducir(self, texto, origen, validador):
        try:
            if origen:
                return self.mod.traducir_estricto(texto, origen=origen, validador=validador)
            return self.mod.traducir_estricto(texto, validador=validador)
        except self.mod.TraduccionFallida as e:
            raise FalloTraduccion(str(e)) from None
        except Exception as e:
            # Un bug del traductor no debe tumbar la ejecucion entera.
            log.exception("Error inesperado en traducir_estricto")
            raise FalloTraduccion(f"inesperado: {type(e).__name__}") from None

    def preparar(self, item):
        """Devuelve (titulo_es, resumen_es). Lanza FalloTraduccion si la
        noticia no es publicable segun la politica estricta."""
        idioma = item["idioma"]
        max_titulo = self.cfg.get("max_largo_titulo", 250)
        max_resumen = self.cfg.get("max_largo_resumen", 700)
        exigir_resumen = self.cfg.get("exigir_resumen_traducido", False)

        titulo = truncar(item["titulo"], max_titulo, sufijo="")
        resumen = item.get("resumen", "") or ""

        if idioma == "es":
            return titulo, truncar(resumen, max_resumen)

        if not self.disponible:
            raise FalloTraduccion("sin traductor")

        if idioma == "ja":
            origen, validador_t = "ja", validador_sin_japones
            # Si el feed no trae cuerpo, se lee el articulo (perezoso: solo
            # despues de que el titulo se haya traducido).
            max_texto = self.cfg.get("max_texto_articulo_ja", 1500)
        else:
            origen, validador_t = None, validador_no_identica(titulo)
            max_texto = max_resumen

        titulo_es = self._traducir(titulo, origen, validador_t)

        if idioma == "ja" and item.get("extraer_articulo") and len(resumen) < 200:
            if self._extraer_articulo:
                resumen = self._extraer_articulo(item["url"]) or resumen

        resumen = truncar(resumen, max_texto, sufijo="")
        resumen_es = ""
        if resumen:
            validador_r = validador_sin_japones if idioma == "ja" else validador_no_identica(resumen)
            try:
                resumen_es = limpiar_html(self._traducir(resumen, origen, validador_r))
            except FalloTraduccion:
                if exigir_resumen:
                    raise
                log.warning(f"Resumen sin traducir, se publica solo el titulo: {titulo[:60]}")
                resumen_es = ""

        return titulo_es, truncar(resumen_es, max_resumen)


class TraductorNulo(Traductor):
    """Para --dry-run sin traductor: devuelve el texto original marcado."""

    def iniciar(self):
        self.proveedor = "nulo"
        return True

    @property
    def disponible(self):
        return True

    def agotado(self):
        return False

    def cerrar(self):
        return "traductor nulo (dry-run)"

    def preparar(self, item):
        titulo = truncar(item["titulo"], self.cfg.get("max_largo_titulo", 250), sufijo="")
        resumen = truncar(item.get("resumen", ""), self.cfg.get("max_largo_resumen", 700))
        if item["idioma"] == "es":
            return titulo, resumen
        return f"[{item['idioma']}] {titulo}", resumen


# =============================================================================
# telegram
#   Cliente minimo de la Bot API de Telegram.
#
#   - Publica en temas (supergrupo en modo foro) con message_thread_id.
#   - Respeta un ritmo minimo entre mensajes (Telegram recomienda no superar
#     ~20 mensajes/minuto en un mismo grupo).
#   - Gestiona 429 (retry_after) y distingue errores permanentes (400) de
#     temporales (5xx, red), para no reintentar para siempre lo que no se puede
#     enviar ni descartar lo que solo fallo por un corte.
#   - Nunca registra la URL de la API: contiene el token.
# =============================================================================

log = logging.getLogger("gear_news.telegram")


@dataclass
class Resultado:
    ok: bool
    message_id: int | None = None
    permanente: bool = False
    error: str = ""


class TelegramInaccesible(Exception):
    """El bot no puede escribir en el chat (403/401): no tiene sentido seguir."""


class Telegram:
    def __init__(self, token, chat_id, cfg, dry_run=False, dormir=time.sleep, reloj=time.monotonic):
        self.token = token
        self.chat_id = chat_id
        tcfg = cfg.get("telegram", {})
        self.ritmo = float(tcfg.get("ritmo_segundos", 3.5))
        self.max_429 = int(tcfg.get("max_reintentos_429", 3))
        self.vista_pequena = bool(tcfg.get("vista_previa_pequena", True))
        self.dry_run = dry_run
        self._dormir = dormir
        self._reloj = reloj
        self._ultimo = None
        self._id_falso = 1000
        self.enviados = []  # en dry-run: registro de lo que se habria enviado

    def _api(self, metodo):
        return f"https://api.telegram.org/bot{self.token}/{metodo}"

    def _esperar_ritmo(self):
        if self._ultimo is not None:
            restante = self.ritmo - (self._reloj() - self._ultimo)
            if restante > 0:
                self._dormir(restante)
        self._ultimo = self._reloj()

    def _llamar(self, metodo, payload):
        """Devuelve Resultado. Reintenta 429 respetando retry_after."""
        for intento in range(self.max_429 + 1):
            self._esperar_ritmo()
            try:
                r = requests.post(self._api(metodo), json=payload, timeout=20)
            except requests.exceptions.RequestException as e:
                return Resultado(False, error=f"red: {type(e).__name__}")

            try:
                cuerpo = r.json()
            except ValueError:
                cuerpo = {}

            if r.status_code == 200 and cuerpo.get("ok"):
                return Resultado(True, message_id=(cuerpo.get("result") or {}).get("message_id"))

            descripcion = cuerpo.get("description", r.text[:200])
            if r.status_code == 429:
                espera = (cuerpo.get("parameters") or {}).get("retry_after", 5)
                log.warning(f"Telegram 429: esperando {espera}s (intento {intento + 1})")
                self._dormir(min(float(espera), 120.0) + 0.5)
                continue
            if r.status_code in (401, 403):
                raise TelegramInaccesible(f"{r.status_code}: {descripcion}")
            if 400 <= r.status_code < 500:
                return Resultado(False, permanente=True, error=f"{r.status_code}: {descripcion}")
            return Resultado(False, error=f"{r.status_code}: {descripcion}")

        return Resultado(False, error="429 persistente")

    # ------------------------------------------------------------------

    def enviar(self, texto, thread_id=None, url_vista_previa=None):
        payload = {"chat_id": self.chat_id, "text": texto, "parse_mode": "HTML"}
        if thread_id is not None:
            payload["message_thread_id"] = int(thread_id)
        if url_vista_previa:
            payload["link_preview_options"] = {
                "url": url_vista_previa, "prefer_small_media": self.vista_pequena}
        else:
            payload["link_preview_options"] = {"is_disabled": True}

        if self.dry_run:
            self._id_falso += 1
            self.enviados.append({"thread_id": thread_id, "texto": texto})
            print(f"\n----- [dry-run] tema={thread_id} -----\n{texto}\n")
            return Resultado(True, message_id=self._id_falso)

        return self._llamar("sendMessage", payload)

    def crear_tema(self, nombre):
        """createForumTopic: requiere que el bot sea admin con permiso
        'Gestionar temas' y que el grupo tenga los temas activados."""
        r = requests.post(self._api("createForumTopic"),
                          json={"chat_id": self.chat_id, "name": nombre}, timeout=20)
        cuerpo = r.json() if r.content else {}
        if not cuerpo.get("ok"):
            raise RuntimeError(cuerpo.get("description", f"HTTP {r.status_code}"))
        return cuerpo["result"]["message_thread_id"]


def enlace_mensaje(chat_id, message_id):
    """Enlace a un mensaje de un supergrupo privado (t.me/c/<id>/<msg>)."""
    texto = str(chat_id)
    if not texto.startswith("-100") or not message_id:
        return None
    return f"https://t.me/c/{texto[4:]}/{message_id}"


# =============================================================================
# publicacion
#   Publicacion: destacadas (cualquier dia), calendario semanal por
#   instrumento, indice semanal opcional y reporte de estado.
#
#   Politica de traduccion estricta (igual que en los bots anteriores): una
#   noticia que no se puede traducir no se publica y se prueba la siguiente.
#   Correcciones respecto a los bots anteriores:
#     - El circuit breaker solo cuenta noticias que NECESITAN traduccion: una
#       fuente en espanol ya no 'demuestra' que el traductor funciona.
#     - Con el traductor caido se siguen publicando las fuentes en espanol.
#     - Una noticia que falla N veces se descarta para siempre (no bloquea).
#     - Un 400 de Telegram descarta la noticia; un 5xx/red la deja pendiente.
#     - Los cupos son por dia: repetir la ejecucion el mismo dia no duplica.
# =============================================================================

log = logging.getLogger("gear_news.publicacion")


class CircuitBreaker:
    """Dos umbrales: estricto mientras no haya NINGUNA traduccion exitosa
    (traductor probablemente caido), tolerante despues (degradacion parcial)."""

    def __init__(self, max_sin_exito=6, max_tras_exito=15):
        self.max_sin_exito = max_sin_exito
        self.max_tras_exito = max_tras_exito
        self.exitos = 0
        self.fallos_consecutivos = 0
        self.motivo = ""

    @property
    def abierto(self):
        return bool(self.motivo)

    def permitir(self):
        if self.abierto:
            return False
        umbral = self.max_tras_exito if self.exitos else self.max_sin_exito
        if self.fallos_consecutivos >= umbral:
            self.motivo = (f"{self.fallos_consecutivos} fallos consecutivos "
                           f"{'tras' if self.exitos else 'sin'} exitos")
            log.error(f"Circuit breaker abierto: {self.motivo}. "
                      f"Solo se publicaran fuentes en espanol.")
            return False
        return True

    def abrir(self, motivo):
        if not self.abierto:
            self.motivo = motivo
            log.error(f"Circuit breaker abierto: {motivo}")

    def exito(self):
        self.exitos += 1
        self.fallos_consecutivos = 0

    def fallo(self):
        self.fallos_consecutivos += 1


class Publicador:
    def __init__(self, cfg, db, telegram, traductor, ahora, tz):
        self.cfg = cfg
        self.db = db
        self.tg = telegram
        self.tr = traductor
        self.ahora = ahora
        self.local = ahora.astimezone(tz)
        self.inicio_dia = self.local.replace(hour=0, minute=0, second=0, microsecond=0)
        self.pcfg = cfg.get("publicacion", {})
        trcfg = cfg.get("traduccion", {})
        self.breaker = CircuitBreaker(trcfg.get("max_fallos_sin_exito", 6),
                                      trcfg.get("max_fallos_tras_exito", 15))
        self.max_intentos = trcfg.get("max_intentos_por_noticia", 3)
        self.temas = cfg.get("telegram", {}).get("temas", {}) or {}
        self.expandible = bool(cfg.get("telegram", {}).get("resumen_expandible", True))
        self.envio_caido = False
        self.fallos_envio_consecutivos = 0
        self.stats = {"por_destino": {}, "descartadas_traduccion": 0, "fallos_envio": 0,
                      "omitidas_sin_traductor": 0, "breaker": ""}

    # ------------------------------------------------------------------
    # Puntuacion y seleccion
    # ------------------------------------------------------------------

    def puntuacion(self, grupo, n_fuentes):
        edad_dias = (self.ahora - desde_iso(grupo["creado_en"])).total_seconds() / 86400
        bonus_tipo = 6 if grupo["tipo"] == "lanzamiento" else 0
        return 10 * n_fuentes + bonus_tipo - 1.5 * edad_dias

    @staticmethod
    def representante(items):
        """Prefiere espanol (no gasta traductor), luego el resumen mas
        completo, luego el primero que llego."""
        return sorted(items, key=lambda i: (i["idioma"] != "es", -len(i["resumen"] or ""), i["id"]))[0]

    def _ordenar(self, grupos):
        con_puntos = []
        for g in grupos:
            n = self.db.n_fuentes(g["id"])
            con_puntos.append((self.puntuacion(g, n), n, g))
        con_puntos.sort(key=lambda t: t[0], reverse=True)
        return con_puntos

    # ------------------------------------------------------------------
    # Nucleo: publicar un lote en un destino
    # ------------------------------------------------------------------

    def _publicar_lote(self, destino, grupos, cupo, destacada=False):
        ya_hoy = self.db.publicadas_desde(self.inicio_dia, destino=destino)
        restante = max(0, cupo - len(ya_hoy))
        registro = self.stats["por_destino"].setdefault(destino, {"publicadas": 0, "cupo": cupo})
        registro["ya_publicadas_hoy"] = len(ya_hoy)
        if restante == 0:
            return 0

        max_por_fuente = self.pcfg.get("max_por_fuente", 2)
        por_fuente = Counter(g["fuente_publicada"] for g in ya_hoy)
        publicadas = 0

        for _, n_fuentes, g in self._ordenar(grupos):
            if publicadas >= restante or self.envio_caido:
                break
            g = self.db.grupo(g["id"])
            if g is None or g["estado"] != "pendiente":
                continue  # p. ej. ya salio como destacada en esta misma ejecucion

            items = self.db.items_de_grupo(g["id"])
            if not items:
                continue
            rep = self.representante(items)
            if por_fuente[rep["fuente"]] >= max_por_fuente:
                continue

            necesita_traduccion = rep["idioma"] != "es"
            if necesita_traduccion:
                if not self.tr.disponible:
                    self.stats["omitidas_sin_traductor"] += 1
                    continue
                if not self.breaker.permitir():
                    self.stats["omitidas_sin_traductor"] += 1
                    continue
                if self.tr.agotado():
                    self.breaker.abrir("todos los proveedores agotados")
                    self.stats["omitidas_sin_traductor"] += 1
                    continue

            try:
                titulo_es, resumen_es = self.tr.preparar(rep)
            except FalloTraduccion as e:
                self.stats["descartadas_traduccion"] += 1
                if necesita_traduccion:
                    self.breaker.fallo()
                definitiva = self.db.marcar_fallo(g["id"], f"traduccion: {e}", self.max_intentos)
                log.warning(f"DESCARTADA{' (definitiva)' if definitiva else ''}: "
                            f"{rep['titulo'][:70]} | {e}")
                continue
            if necesita_traduccion:
                self.breaker.exito()

            if self._enviar(g, rep, titulo_es, resumen_es, destino, destacada, n_fuentes):
                publicadas += 1
                por_fuente[rep["fuente"]] += 1
                log.info(f"[{destino} {publicadas}/{restante}] {rep['fuente']}: {rep['titulo'][:70]}")

        registro["publicadas"] += publicadas
        return publicadas

    def _enviar(self, g, rep, titulo_es, resumen_es, destino, destacada, n_fuentes):
        inst_cfg = self.cfg["instrumentos"][g["instrumento"]]
        item = dict(rep)
        item["marcas"] = _json_lista(rep.get("marcas"))
        thread = self.temas.get(destino)

        texto = mensaje_noticia(item, titulo_es, resumen_es, inst_cfg, self.cfg,
                                destacada=destacada, n_fuentes=n_fuentes, expandible=self.expandible)
        res = self.tg.enviar(texto, thread_id=thread, url_vista_previa=rep["url"])

        if not res.ok and res.permanente and self.expandible and resumen_es:
            # Reintento con formato simple (sin blockquote) por si el 400 era
            # de formato: no se descarta una noticia por la plantilla.
            log.warning(f"Telegram rechazo el mensaje ({res.error}); reintento en formato simple")
            texto = mensaje_noticia(item, titulo_es, resumen_es, inst_cfg, self.cfg,
                                    destacada=destacada, n_fuentes=n_fuentes, expandible=False)
            res = self.tg.enviar(texto, thread_id=thread, url_vista_previa=rep["url"])

        if res.ok:
            self.fallos_envio_consecutivos = 0
            self.db.marcar_publicada(g["id"], destino, res.message_id, self.ahora,
                                     titulo=titulo_es, fuente=rep["fuente"])
            return True

        self.stats["fallos_envio"] += 1
        if res.permanente:
            self.db.marcar_descartada(g["id"], f"telegram {res.error}")
            log.error(f"Descartada por Telegram ({res.error}): {rep['titulo'][:70]}")
        else:
            self.fallos_envio_consecutivos += 1
            log.warning(f"Fallo temporal de envio ({res.error}); queda pendiente")
            if self.fallos_envio_consecutivos >= 2:
                self.envio_caido = True
                log.error("Telegram no responde: se detiene la publicacion de esta ejecucion")
        return False

    # ------------------------------------------------------------------
    # Pasos
    # ------------------------------------------------------------------

    def destacadas(self):
        dcfg = self.pcfg.get("destacadas", {})
        if not dcfg.get("activo", True):
            return 0
        desde = self.ahora - timedelta(hours=dcfg.get("ventana_horas", 48))
        minimo = dcfg.get("fuentes_minimas", 3)
        candidatos = [g for g in self.db.pendientes(desde)
                      if self.db.n_fuentes(g["id"]) >= minimo]
        if not candidatos:
            self.stats["por_destino"].setdefault(
                "destacadas", {"publicadas": 0, "cupo": dcfg.get("max_por_dia", 3)})
            return 0
        return self._publicar_lote("destacadas", candidatos, dcfg.get("max_por_dia", 3),
                                   destacada=True)

    def calendario(self, dia=None):
        dia = dia or nombre_dia(self.local)
        plan = (self.pcfg.get("calendario") or {}).get(dia) or {}
        desde = self.ahora - timedelta(days=self.cfg["general"].get("dias_en_pool", 10))
        total = 0
        for instrumento, cupo in plan.items():
            if instrumento not in self.cfg["instrumentos"]:
                log.warning(f"Calendario: instrumento desconocido '{instrumento}'")
                continue
            candidatos = self.db.pendientes(desde, instrumento=instrumento)
            total += self._publicar_lote(instrumento, candidatos, int(cupo))
        return total

    def indice_semanal(self, dia=None):
        icfg = self.pcfg.get("indice_semanal", {})
        dia = dia or nombre_dia(self.local)
        if not icfg.get("activo", False) or dia != icfg.get("dia", "domingo"):
            return False
        anio, semana, _ = self.local.isocalendar()
        clave = f"indice-{anio}-{semana:02d}"
        if self.db.envio_hecho(clave):
            return False
        grupos = self.db.publicadas_desde(self.ahora - timedelta(days=7))
        if not grupos:
            return False
        chat_id = self.tg.chat_id
        filas = []
        orden = list(self.cfg["instrumentos"].keys())
        for g in sorted(grupos, key=lambda x: (orden.index(x["instrumento"])
                                                if x["instrumento"] in orden else 99)):
            emoji = self.cfg["instrumentos"].get(g["instrumento"], {}).get("emoji", "•")
            filas.append((emoji, g["titulo_publicado"] or g["tokens"],
                          enlace_mensaje(chat_id, g["message_id"])))
        inicio = (self.local - timedelta(days=6)).strftime("%d/%m")
        texto = mensaje_indice(f"Índice de la semana ({inicio}–{self.local.strftime('%d/%m')})", filas)
        res = self.tg.enviar(texto, thread_id=self.temas.get("destacadas"))
        if res.ok:
            self.db.marcar_envio(clave, self.ahora)
        return res.ok

    def ejecutar(self, dia=None):
        dia = dia or nombre_dia(self.local)
        log.info(f"Publicacion del {dia} {self.local:%d/%m/%Y %H:%M}")
        self.destacadas()
        self.calendario(dia)
        self.indice_semanal(dia)
        self.stats["breaker"] = self.breaker.motivo
        self.stats["dia"] = dia
        return self.stats


def _json_lista(valor):
    import json
    if isinstance(valor, list):
        return valor
    try:
        return json.loads(valor or "[]")
    except ValueError:
        return []


# =============================================================================
# main
#   Gear News: bot unificado de noticias (guitarra, bajo, teclados, bateria,
#   pro audio) para Telegram con temas, calendario semanal y sin repeticiones.
#
#   Sin comando equivale a `diario` (compatible con el telegram_bot.py anterior).
#
#   Comandos:
#     python main.py recolectar          # lee feeds y llena el pool (varias veces al dia)
#     python main.py publicar            # destacadas + calendario del dia + indice
#     python main.py diario              # recolectar y luego publicar
#     python main.py estado              # resumen del pool y feeds por consola
#     python main.py validar-feeds       # comprueba todas las URLs de config.yaml
#     python main.py crear-temas         # crea los temas del foro e imprime sus IDs
#     python main.py migrar a.json b.json  # importa historiales de los bots anteriores
#
#   Opciones globales: --config RUTA  --dry-run  --dia lunes  -v
#   Variables de entorno: TOKEN, CHAT_ID (las mismas que tus bots actuales).
# =============================================================================

log = logging.getLogger("gear_news")

# Configuracion integrada (dict). None en el paquete: se usa config.yaml.
# En el telegram_bot.py de un solo archivo contiene la configuracion completa.


# ---------------------------------------------------------------------------
# Infraestructura
# ---------------------------------------------------------------------------

@contextmanager
def bloqueo(ruta):
    """Evita dos ejecuciones simultaneas sobre la misma base de datos."""
    try:
        import fcntl
    except ImportError:  # Windows: sin bloqueo (ejecuta una sola instancia)
        yield
        return
    f = open(ruta, "w")
    try:
        fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        f.close()
        log.error("Otra ejecucion esta en curso; se sale sin hacer nada.")
        sys.exit(2)
    try:
        yield
    finally:
        fcntl.flock(f, fcntl.LOCK_UN)
        f.close()


def crear_telegram(cfg, args):
    token, chat_id = os.getenv("TOKEN"), os.getenv("CHAT_ID")
    if args.dry_run:
        return Telegram(token or "dry", chat_id or "-1000000000000", cfg, dry_run=True)
    if not token or not chat_id:
        log.error("Faltan las variables de entorno TOKEN y/o CHAT_ID.")
        sys.exit(1)
    return Telegram(token, chat_id, cfg)


def crear_traductor(cfg, args):
    if args.dry_run and args.sin_traduccion:
        t = TraductorNulo(cfg)
    else:
        t = Traductor(cfg, extraer_articulo=feeds.extraer_articulo)
    t.iniciar()
    return t


# ---------------------------------------------------------------------------
# Comandos
# ---------------------------------------------------------------------------

def cmd_recolectar(cfg, db, args, ahora):
    stats = recolectar(cfg, db, Clasificador(cfg), ahora)
    db.registrar_ejecucion("recolectar", stats, ahora)
    log.info(f"Recoleccion: {stats}")
    return stats


def cmd_publicar(cfg, db, args, ahora, tz, stats_recoleccion=None):
    tg = crear_telegram(cfg, args)
    tr = crear_traductor(cfg, args)
    pub = Publicador(cfg, db, tg, tr, ahora, tz)
    try:
        stats = pub.ejecutar(dia=args.dia)
    except TelegramInaccesible as e:
        log.error(f"El bot no puede escribir en el chat: {e}")
        stats = dict(pub.stats, error=str(e))
    stats_tr = tr.cerrar()
    if stats_tr:
        log.info(stats_tr)

    datos = {
        "dia": stats.get("dia", args.dia or ""),
        "publicacion": stats,
        "proveedor": tr.proveedor,
        "pool": db.resumen_pool(ahora - _dias(cfg)),
        "fuentes_problemas": db.fuentes_con_problemas(
            cfg["publicacion"].get("alerta_feed_fallos", 2)),
    }
    if stats_recoleccion:
        datos["recoleccion"] = stats_recoleccion
    db.registrar_ejecucion("publicar", datos, ahora)

    tema_estado = (cfg["telegram"].get("temas") or {}).get("estado")
    if cfg["publicacion"].get("reporte_estado", True) and tema_estado is not None:
        try:
            tg.enviar(mensaje_estado(ahora.astimezone(tz), datos), thread_id=tema_estado)
        except TelegramInaccesible:
            pass
    return stats


def _importar_lista_urls(db, ruta, ahora):
    with open(ruta, encoding="utf-8") as f:
        urls = json.load(f)
    if not isinstance(urls, list):
        raise ValueError("se esperaba una lista de URLs")
    n = 0
    for url in urls:
        if isinstance(url, str) and url.strip():
            db.registrar_historial(normalizar_url(url), "", "migrada", ahora)
            n += 1
    db.commit()
    return n


def sincronizar_historiales(cfg, db, ahora):
    """Importa en cada ejecucion los historiales JSON de los bots anteriores
    (INSERT OR IGNORE: es barato e idempotente). Asi nada de lo ya enviado
    se repite, aunque la base de datos se haya perdido."""
    for ruta in cfg["general"].get("historiales_json", []) or []:
        if not os.path.exists(ruta):
            continue
        try:
            n = _importar_lista_urls(db, ruta, ahora)
            log.debug(f"{ruta}: {n} URLs sincronizadas")
        except (OSError, ValueError) as e:
            log.error(f"No se pudo leer {ruta}: {e}")


def escribir_espejo(cfg, db):
    """Escribe las URLs ya publicadas en un JSON (mismo formato que el
    historial del bot anterior). Si tu despliegue solo versiona ese JSON y no
    gear_news.db, este archivo sigue impidiendo repeticiones."""
    ruta = cfg["general"].get("historial_espejo")
    if not ruta:
        return
    urls = db.urls_historial(cfg["general"].get("max_historial_espejo", 5000))
    temporal = f"{ruta}.tmp"
    with open(temporal, "w", encoding="utf-8") as f:
        json.dump(urls, f, ensure_ascii=False, indent=2)
    os.replace(temporal, ruta)


def cmd_estado(cfg, db, args, ahora):
    print("Pool pendiente por instrumento:", db.resumen_pool(ahora - _dias(cfg)))
    problemas = db.fuentes_con_problemas(1)
    print(f"Feeds con fallos ({len(problemas)}):")
    for f in problemas:
        print(f"  - {f['nombre']}: {f['ultimo_error']} (x{f['fallos_consecutivos']})")
    hoy = ahora.replace(hour=0, minute=0, second=0)
    print("Publicadas en las ultimas 24 h:", len(db.publicadas_desde(hoy)))


def cmd_validar_feeds(cfg, args):
    """Comprueba cada feed: estado, n.º de entradas, fecha de la mas reciente."""
    print(f"{'FUENTE':32} {'ESTADO':8} {'ENTR':>4}  {'MAS RECIENTE':16}  DETALLE")
    malos = 0
    for f in cfg["fuentes"]:
        entradas, error = feeds.leer_fuente(f["url"], cfg["general"].get("timeout_http", 15))
        activa = "" if f.get("activa", True) else " (inactiva)"
        if error:
            malos += 1
            print(f"{f['nombre'][:32]:32} {'ERROR':8} {0:>4}  {'-':16}  {error}{activa}")
            continue
        fechas = [e.fecha for e in entradas if e.fecha]
        reciente = max(fechas).strftime("%Y-%m-%d %H:%M") if fechas else "sin fechas"
        print(f"{f['nombre'][:32]:32} {'OK':8} {len(entradas):>4}  {reciente:16}  {activa}")
    print(f"\n{len(cfg['fuentes']) - malos}/{len(cfg['fuentes'])} feeds responden.")
    return malos


def cmd_crear_temas(cfg, args):
    tg = crear_telegram(cfg, args)
    nombres = {"destacadas": "⭐ Destacadas", "estado": "📊 Estado del bot"}
    for clave, icfg in cfg["instrumentos"].items():
        nombres[clave] = f"{icfg.get('emoji', '')} {icfg['nombre']}".strip()
    print("Pega estos IDs en telegram.temas de config.yaml:\n")
    for clave in ["destacadas", *cfg["instrumentos"].keys(), "estado"]:
        if args.dry_run:
            print(f"  {clave}: <id>   # {nombres[clave]}")
            continue
        try:
            tid = tg.crear_tema(nombres[clave])
            print(f"  {clave}: {tid}")
        except Exception as e:
            print(f"  {clave}: ERROR {e}")


def cmd_migrar(cfg, db, args, ahora):
    """Importa los historiales JSON de los bots anteriores (listas de URLs)
    para que nada de lo ya enviado vuelva a publicarse."""
    total = 0
    for ruta in args.archivos:
        try:
            n = _importar_lista_urls(db, ruta, ahora)
        except (OSError, ValueError) as e:
            log.error(f"No se pudo leer {ruta}: {e}")
            continue
        log.info(f"{ruta}: {n} URLs importadas al historial")
        total += n
    return total


def _dias(cfg):
    from datetime import timedelta
    return timedelta(days=cfg["general"].get("dias_en_pool", 10))


# ---------------------------------------------------------------------------

def main(argv=None):
    p = argparse.ArgumentParser(description="Gear News bot")
    p.add_argument("comando", nargs="?", default="diario",
                   choices=["recolectar", "publicar", "diario", "estado",
                            "validar-feeds", "crear-temas", "migrar"])
    p.add_argument("archivos", nargs="*", help="(migrar) historiales JSON")
    p.add_argument("--config", default="config.yaml")
    p.add_argument("--dry-run", action="store_true",
                   help="no envia nada a Telegram; imprime los mensajes")
    p.add_argument("--sin-traduccion", action="store_true",
                   help="(con --dry-run) no usa traductor.py; muestra textos originales")
    p.add_argument("--dia", choices=NOMBRE_DIAS, help="fuerza el dia del calendario")
    p.add_argument("-v", "--verbose", action="store_true")
    args = p.parse_args(argv)

    logging.basicConfig(level=logging.DEBUG if args.verbose else logging.INFO,
                        format="%(asctime)s [%(levelname)s] %(name)s: %(message)s",
                        datefmt="%Y-%m-%d %H:%M:%S")
    # Nunca registrar URLs de requests/urllib3 a nivel DEBUG: llevan el token.
    logging.getLogger("urllib3").setLevel(logging.WARNING)

    try:
        cfg = config_mod.cargar(args.config, por_defecto=CONFIG_INTEGRADA)
    except (OSError, config_mod.ErrorConfig) as e:
        log.error(str(e))
        return 1

    socket.setdefaulttimeout(cfg["general"].get("timeout_http", 15) + 5)
    tz = ZoneInfo(cfg["general"].get("zona_horaria", "UTC"))
    ahora = datetime.now(timezone.utc)

    if args.comando == "validar-feeds":
        return 1 if cmd_validar_feeds(cfg, args) else 0
    if args.comando == "crear-temas":
        cmd_crear_temas(cfg, args)
        return 0

    ruta_db = cfg["general"].get("base_datos", "gear_news.db")
    with bloqueo(ruta_db + ".lock"):
        db = BaseDatos.copia_en_memoria(ruta_db) if args.dry_run else BaseDatos(ruta_db)
        if args.dry_run:
            log.info("DRY-RUN: se trabaja sobre una copia en memoria; la base real no cambia.")
        try:
            if args.comando in ("recolectar", "publicar", "diario"):
                sincronizar_historiales(cfg, db, ahora)
            if args.comando == "recolectar":
                cmd_recolectar(cfg, db, args, ahora)
            elif args.comando == "publicar":
                cmd_publicar(cfg, db, args, ahora, tz)
            elif args.comando == "diario":
                stats = cmd_recolectar(cfg, db, args, ahora)
                cmd_publicar(cfg, db, args, datetime.now(timezone.utc), tz, stats)
            elif args.comando == "estado":
                cmd_estado(cfg, db, args, ahora)
            elif args.comando == "migrar":
                cmd_migrar(cfg, db, args, ahora)
            if args.comando in ("publicar", "diario", "migrar") and not args.dry_run:
                escribir_espejo(cfg, db)
        finally:
            db.cerrar()
    return 0



# =============================================================================
# CONFIGURACION INTEGRADA
#   Equivale a config.yaml del paquete. Si existe un config.yaml en la carpeta
#   de ejecucion, se usa ese en su lugar.
#
#   Lo que mas se suele tocar:
#     telegram.temas          IDs de los temas (python telegram_bot.py crear-temas)
#     publicacion.calendario  cupos por dia e instrumento
#     publicacion.destacadas  fuentes_minimas / ventana_horas / max_por_dia
#     instrumentos.*          palabras_clave y exclusiones (limites de palabra)
#     fuentes                 'activa': False desactiva; las URLs no confirmadas
#                             conviene validarlas con: validar-feeds
# =============================================================================

CONFIG_INTEGRADA = {'general': {'zona_horaria': 'America/Tijuana',
             'base_datos': 'gear_news.db',
             'dias_en_pool': 10,
             'antiguedad_max_entrada_dias': 10,
             'dias_historial_titulos': 45,
             'dias_historial_urls': 365,
             'max_entradas_por_feed': 25,
             'timeout_http': 15,
             'pausa_entre_feeds': 1,
             'historiales_json': ['noticias_enviadas.json', 'noticias_enviadas_bass.json'],
             'historial_espejo': 'noticias_enviadas.json',
             'max_historial_espejo': 5000},
 'telegram': {'temas': {'destacadas': None,
                        'guitarra': None,
                        'bajo': None,
                        'teclados': None,
                        'bateria': None,
                        'proaudio': None,
                        'estado': None},
              'ritmo_segundos': 3.5,
              'max_reintentos_429': 3,
              'resumen_expandible': True,
              'vista_previa_pequena': True},
 'agrupacion': {'ventana_horas': 72,
                'umbral_jaccard': 0.7,
                'umbral_solapamiento': 0.8,
                'min_tokens_comunes': 3},
 'traduccion': {'exigir_resumen_traducido': False,
                'max_fallos_sin_exito': 6,
                'max_fallos_tras_exito': 15,
                'max_intentos_por_noticia': 3,
                'max_largo_titulo': 250,
                'max_largo_resumen': 700,
                'max_texto_articulo_ja': 1500},
 'publicacion': {'max_por_fuente': 2,
                 'largo_resumen_visible': 300,
                 'alerta_feed_fallos': 2,
                 'reporte_estado': True,
                 'calendario': {'lunes': {'guitarra': 5},
                                'martes': {'bajo': 4},
                                'miercoles': {'teclados': 4},
                                'jueves': {'bateria': 4},
                                'viernes': {'proaudio': 4},
                                'sabado': {'guitarra': 5, 'bajo': 3},
                                'domingo': {'guitarra': 2,
                                            'bajo': 1,
                                            'teclados': 1,
                                            'bateria': 1,
                                            'proaudio': 1}},
                 'destacadas': {'activo': True,
                                'fuentes_minimas': 3,
                                'ventana_horas': 48,
                                'max_por_dia': 3},
                 'indice_semanal': {'activo': False, 'dia': 'domingo'}},
 'clasificacion': {'excluir_ofertas': True,
                   'patrones_oferta': ['deal',
                                       'deals',
                                       'black friday',
                                       'cyber monday',
                                       'prime day',
                                       '% off',
                                       'save',
                                       'discount',
                                       'sale ends',
                                       'price drop',
                                       'oferta',
                                       'descuento'],
                   'patrones_ruido': ['appoints',
                                      'appointed',
                                      'names',
                                      'named',
                                      'hires',
                                      'promotes',
                                      'promoted',
                                      'distribution',
                                      'distributor',
                                      'distributes',
                                      'represent',
                                      'represents',
                                      'partners with',
                                      'installs',
                                      'installed',
                                      'installation',
                                      'house of worship',
                                      'church',
                                      'webinar',
                                      'ebook',
                                      'nombra',
                                      'ficha',
                                      'distribuira'],
                   'patrones_lanzamiento': ['unveils',
                                            'announces',
                                            'launches',
                                            'introduces',
                                            'releases',
                                            'debuts',
                                            'reveals',
                                            'firmware',
                                            'update',
                                            'acquires',
                                            'acquisition',
                                            'presenta',
                                            'lanza',
                                            'anuncia',
                                            'adquiere']},
 'marcas': ['Fender',
            'Gibson',
            'Ibanez',
            'PRS',
            'Schecter',
            'ESP',
            'Jackson',
            'Charvel',
            'Suhr',
            'Vigier',
            'Strandberg',
            'Music Man',
            'Line 6',
            'Fractal Audio',
            'Kemper',
            'Neural DSP',
            'Boss',
            'Marshall',
            'Mesa Boogie',
            'EVH',
            'Darkglass',
            'Fodera',
            'Spector',
            'Warwick',
            'Sadowsky',
            'Ampeg',
            'Markbass',
            'Yamaha',
            'Roland',
            'Korg',
            'Nord',
            'Moog',
            'Sequential',
            'Arturia',
            'Behringer',
            'Kawai',
            'Zildjian',
            'Sabian',
            'Meinl',
            'Paiste',
            'Tama',
            'Pearl',
            'DW',
            'Ludwig',
            'Gretsch',
            'Sonor',
            'Alesis',
            'EFNOTE',
            'Neve',
            'SSL',
            'Universal Audio',
            'RME',
            'Neumann',
            'Shure',
            'Sennheiser',
            'Genelec',
            'DiGiCo',
            'Allen & Heath',
            'Midas',
            'L-Acoustics',
            'Meyer Sound',
            'Avid',
            'Steinberg'],
 'instrumentos': {'guitarra': {'nombre': 'Guitarra',
                               'emoji': '🎸',
                               'hashtag': 'guitarra',
                               'filtrar_ruido': True,
                               'palabras_clave': ['guitar',
                                                  'guitarist',
                                                  'electric guitar',
                                                  'guitar amp',
                                                  'guitar amplifier',
                                                  'guitar pedal',
                                                  'pedalboard',
                                                  'overdrive',
                                                  'fuzz pedal',
                                                  'distortion pedal',
                                                  'amp modeler',
                                                  'amp sim',
                                                  'amp capture',
                                                  'profiling amp',
                                                  'cab sim',
                                                  'impulse response',
                                                  'ir loader',
                                                  'multi-effects',
                                                  'superstrat',
                                                  'seven-string',
                                                  'eight-string',
                                                  'signature guitar',
                                                  'shred',
                                                  'djent',
                                                  'Line 6 Helix',
                                                  'Helix',
                                                  'Fractal Audio',
                                                  'Axe-Fx',
                                                  'FM3',
                                                  'FM9',
                                                  'Kemper',
                                                  'Neural DSP',
                                                  'Quad Cortex',
                                                  'Boss pedal',
                                                  'Fender',
                                                  'Gibson',
                                                  'Ibanez',
                                                  'PRS',
                                                  'Schecter',
                                                  'Charvel',
                                                  'Suhr',
                                                  'Vigier',
                                                  'Tom Anderson',
                                                  'Strandberg',
                                                  'Jackson guitars',
                                                  'ESP guitars',
                                                  'EVH',
                                                  'Mesa Boogie',
                                                  'Marshall amp',
                                                  'John Petrucci',
                                                  'Steve Vai',
                                                  'Joe Satriani',
                                                  'Tosin Abasi',
                                                  'Tim Henson',
                                                  'Plini',
                                                  'Synyster Gates',
                                                  'Zakk Wylde',
                                                  'Yngwie',
                                                  'Paul Gilbert',
                                                  'Guthrie Govan',
                                                  'guitarra',
                                                  'guitarrista',
                                                  'pedal de efectos'],
                               'exclusiones': ['bass guitar', 'bassist', 'drummer', 'keyboardist']},
                  'bajo': {'nombre': 'Bajo',
                           'emoji': '🎵',
                           'hashtag': 'bajo',
                           'filtrar_ruido': True,
                           'palabras_clave': ['bass guitar',
                                              'bassist',
                                              'bass player',
                                              'electric bass',
                                              'upright bass',
                                              'double bass',
                                              'fretless',
                                              'slap bass',
                                              'bass amp',
                                              'bass pedal',
                                              'bass preamp',
                                              'bass di',
                                              'five-string bass',
                                              'extended range bass',
                                              'Fodera',
                                              'Darkglass',
                                              'Spector',
                                              'Warwick',
                                              'Sadowsky',
                                              'Ampeg',
                                              'Markbass',
                                              'Aguilar',
                                              'Precision Bass',
                                              'Jazz Bass',
                                              'StingRay',
                                              'Victor Wooten',
                                              'Marcus Miller',
                                              'Geddy Lee',
                                              'Billy Sheehan',
                                              'John Myung',
                                              'Les Claypool',
                                              'bajista',
                                              'bajo electrico',
                                              'contrabajo'],
                           'exclusiones': ['bass music', 'bass boost', 'bass fishing', 'bassoon']},
                  'teclados': {'nombre': 'Teclados',
                               'emoji': '🎹',
                               'hashtag': 'teclados',
                               'filtrar_ruido': True,
                               'palabras_clave': ['synth',
                                                  'synthesizer',
                                                  'polysynth',
                                                  'keyboardist',
                                                  'stage piano',
                                                  'digital piano',
                                                  'workstation',
                                                  'hammond',
                                                  'rhodes',
                                                  'wurlitzer',
                                                  'clavinet',
                                                  'mellotron',
                                                  'keytar',
                                                  'aftertouch',
                                                  'mpe',
                                                  'Nord Stage',
                                                  'Nord Lead',
                                                  'Nord Electro',
                                                  'Montage',
                                                  'MODX',
                                                  'Fantom',
                                                  'Kronos',
                                                  'Nautilus',
                                                  'Juno',
                                                  'Jupiter',
                                                  'Prophet',
                                                  'Oberheim',
                                                  'Moog',
                                                  'Sequential',
                                                  'Arturia',
                                                  'minilogue',
                                                  'microKorg',
                                                  'Pianoteq',
                                                  'Keyscape',
                                                  'Omnisphere',
                                                  'Jordan Rudess',
                                                  'Derek Sherinian',
                                                  'Rick Wakeman',
                                                  'Jens Johansson',
                                                  'tecladista',
                                                  'sintetizador',
                                                  'piano digital'],
                               'exclusiones': ['mechanical keyboard',
                                               'gaming keyboard',
                                               'magic keyboard',
                                               'guitar synth',
                                               'drum machine',
                                               'drum synth']},
                  'bateria': {'nombre': 'Batería',
                              'emoji': '🥁',
                              'hashtag': 'bateria',
                              'filtrar_ruido': True,
                              'palabras_clave': ['drummer',
                                                 'drumset',
                                                 'drum kit',
                                                 'drum set',
                                                 'snare drum',
                                                 'cymbal',
                                                 'hi-hat',
                                                 'ride cymbal',
                                                 'crash cymbal',
                                                 'double pedal',
                                                 'bass drum pedal',
                                                 'drumhead',
                                                 'drumsticks',
                                                 'electronic drums',
                                                 'e-drums',
                                                 'V-Drums',
                                                 'drum module',
                                                 'drum trigger',
                                                 'percussion',
                                                 'cajon',
                                                 'Zildjian',
                                                 'Sabian',
                                                 'Meinl',
                                                 'Paiste',
                                                 'Tama',
                                                 'Pearl drums',
                                                 'DW drums',
                                                 'Drum Workshop',
                                                 'Ludwig',
                                                 'Gretsch drums',
                                                 'Mapex',
                                                 'Sonor',
                                                 'Evans drumheads',
                                                 'Remo',
                                                 'Vic Firth',
                                                 'Promark',
                                                 'SPD-SX',
                                                 'EFNOTE',
                                                 'Superior Drummer',
                                                 'EZdrummer',
                                                 'GetGood Drums',
                                                 'Mike Portnoy',
                                                 'Mike Mangini',
                                                 'Gavin Harrison',
                                                 'George Kollias',
                                                 'Thomas Lang',
                                                 'Eloy Casagrande',
                                                 'Matt Garstka',
                                                 'Anika Nilles',
                                                 'Benny Greb',
                                                 'Virgil Donati',
                                                 'Marco Minnemann',
                                                 'baterista',
                                                 'platillos',
                                                 'redoblante',
                                                 'baquetas',
                                                 'bateria electronica',
                                                 'bateria acustica'],
                              'exclusiones': ['drum and bass',
                                              'drum & bass',
                                              'dnb',
                                              'drum machine',
                                              'drum sampler',
                                              'sample pack',
                                              'groovebox',
                                              'beatmaker',
                                              'eardrum',
                                              'drum up']},
                  'proaudio': {'nombre': 'Pro Audio',
                               'emoji': '🎛️',
                               'hashtag': 'proaudio',
                               'filtrar_ruido': True,
                               'palabras_clave': ['audio interface',
                                                  'mic preamp',
                                                  'preamp',
                                                  'condenser microphone',
                                                  'ribbon mic',
                                                  'studio monitor',
                                                  'nearfield',
                                                  'mixing console',
                                                  'channel strip',
                                                  'mastering',
                                                  'Dolby Atmos',
                                                  'immersive audio',
                                                  'Pro Tools',
                                                  'DAW',
                                                  'plug-in',
                                                  'plugin',
                                                  'FOH',
                                                  'front of house',
                                                  'monitor engineer',
                                                  'line array',
                                                  'PA system',
                                                  'in-ear monitor',
                                                  'wireless system',
                                                  'digital console',
                                                  'stagebox',
                                                  'AoIP',
                                                  'audio over IP',
                                                  'Dante network',
                                                  'AES67',
                                                  'ST 2110',
                                                  'Ravenna',
                                                  'Milan AVB',
                                                  'DSP',
                                                  'transducer',
                                                  'acoustic measurement',
                                                  'Smaart',
                                                  'Neve',
                                                  'SSL',
                                                  'Universal Audio',
                                                  'RME',
                                                  'Apogee',
                                                  'Neumann',
                                                  'Shure',
                                                  'Sennheiser',
                                                  'DPA',
                                                  'Genelec',
                                                  'ADAM Audio',
                                                  'DiGiCo',
                                                  'Allen & Heath',
                                                  'Midas',
                                                  'L-Acoustics',
                                                  'd&b audiotechnik',
                                                  'Meyer Sound',
                                                  'Martin Audio',
                                                  'Lawo',
                                                  'Calrec',
                                                  'audio profesional',
                                                  'sonido en directo',
                                                  'consola de mezcla',
                                                  'monitores de estudio',
                                                  'ingeniero de sonido'],
                               'exclusiones': ['gaming headset', 'home theater', 'soundbar'],
                               'segmentos': {'Estudio': ['audio interface',
                                                         'preamp',
                                                         'condenser microphone',
                                                         'studio monitor',
                                                         'nearfield',
                                                         'mastering',
                                                         'Dolby Atmos',
                                                         'Pro Tools',
                                                         'DAW',
                                                         'plugin',
                                                         'channel strip'],
                                             'Directo': ['FOH',
                                                         'front of house',
                                                         'line array',
                                                         'in-ear monitor',
                                                         'monitor engineer',
                                                         'stagebox',
                                                         'tour',
                                                         'PA system',
                                                         'wireless system'],
                                             'Broadcast': ['AoIP',
                                                           'ST 2110',
                                                           'broadcast',
                                                           'radio',
                                                           'intercom',
                                                           'Lawo',
                                                           'Calrec'],
                                             'Ingenieria': ['DSP',
                                                            'transducer',
                                                            'measurement',
                                                            'Smaart',
                                                            'amplifier design']}}},
 'fuentes': [{'nombre': 'Young Guitar',
              'url': 'https://youngguitar.jp/feed/',
              'idioma': 'ja',
              'instrumentos': ['guitarra'],
              'especializada': True,
              'extraer_articulo': True},
             {'nombre': 'Guitar World',
              'url': 'https://www.guitarworld.com/feeds/all',
              'instrumentos': ['guitarra', 'bajo'],
              'editorial': 'future'},
             {'nombre': 'Guitar Player',
              'url': 'https://www.guitarplayer.com/feeds/all',
              'instrumentos': ['guitarra', 'bajo'],
              'editorial': 'future'},
             {'nombre': 'Total Guitar',
              'url': 'https://www.musicradar.com/total-guitar/rss',
              'instrumentos': ['guitarra'],
              'editorial': 'future'},
             {'nombre': 'Guitar Techniques',
              'url': 'https://www.musicradar.com/guitar-techniques/rss',
              'instrumentos': ['guitarra'],
              'editorial': 'future'},
             {'nombre': 'Ultimate Guitar',
              'url': 'https://www.ultimate-guitar.com/rss/news',
              'instrumentos': ['guitarra', 'bajo', 'bateria']},
             {'nombre': 'Premier Guitar',
              'url': 'https://www.premierguitar.com/feeds/news',
              'instrumentos': ['guitarra', 'bajo']},
             {'nombre': 'Reverb News',
              'url': 'https://reverb.com/news/rss',
              'instrumentos': ['guitarra', 'bajo', 'teclados', 'bateria']},
             {'nombre': 'Sweetwater InSync',
              'url': 'https://www.sweetwater.com/insync/feed/',
              'instrumentos': ['guitarra', 'bajo', 'teclados', 'bateria', 'proaudio']},
             {'nombre': 'Gearnews Guitar',
              'url': 'https://www.gearnews.com/zone/guitar/feed/',
              'instrumentos': ['guitarra', 'bajo'],
              'editorial': 'gearnews'},
             {'nombre': 'Guitar.com',
              'url': 'https://guitar.com/feed/',
              'instrumentos': ['guitarra', 'bajo']},
             {'nombre': 'Guitar Interactive',
              'url': 'https://guitarinteractivemagazine.com/feed/',
              'instrumentos': ['guitarra', 'bajo']},
             {'nombre': 'Vintage Guitar',
              'url': 'https://www.vintageguitar.com/feed/',
              'instrumentos': ['guitarra', 'bajo']},
             {'nombre': 'Acoustic Guitar',
              'url': 'https://acousticguitar.com/feed/',
              'instrumentos': ['guitarra'],
              'especializada': True},
             {'nombre': 'Jazz Guitar Today',
              'url': 'https://jazzguitartoday.com/feed/',
              'instrumentos': ['guitarra'],
              'especializada': True},
             {'nombre': 'Classical Guitar',
              'url': 'https://classicalguitarmagazine.com/feed/',
              'instrumentos': ['guitarra'],
              'especializada': True},
             {'nombre': 'Metal Injection',
              'url': 'https://metalinjection.net/feed',
              'instrumentos': ['guitarra', 'bajo', 'bateria']},
             {'nombre': 'Louder Sound',
              'url': 'https://www.loudersound.com/feeds/all',
              'instrumentos': ['guitarra', 'bajo', 'bateria'],
              'editorial': 'future'},
             {'nombre': 'Blabbermouth',
              'url': 'https://blabbermouth.net/feed',
              'instrumentos': ['guitarra', 'bajo', 'bateria']},
             {'nombre': 'MusicRadar',
              'url': 'https://www.musicradar.com/rss',
              'instrumentos': ['guitarra', 'bajo', 'teclados', 'bateria', 'proaudio'],
              'editorial': 'future'},
             {'nombre': 'KVR Audio',
              'url': 'https://www.kvraudio.com/news.rss',
              'instrumentos': ['proaudio', 'teclados', 'guitarra', 'bateria']},
             {'nombre': 'Gearspace Pro Audio News',
              'url': 'https://gearspace.com/forums/pro-audio-news.539/index.rss',
              'instrumentos': ['proaudio', 'guitarra', 'teclados']},
             {'nombre': 'Bass Player Mexico',
              'url': 'https://bassplayermexico.com/feed/',
              'idioma': 'es',
              'instrumentos': ['bajo'],
              'especializada': True},
             {'nombre': 'No Treble',
              'url': 'https://www.notreble.com/feed/',
              'instrumentos': ['bajo'],
              'especializada': True},
             {'nombre': 'Bass Magazine',
              'url': 'https://bassmagazine.com/feed/',
              'instrumentos': ['bajo'],
              'especializada': True},
             {'nombre': 'Bass Musician Magazine',
              'url': 'https://bassmusicianmagazine.com/feed/',
              'instrumentos': ['bajo'],
              'especializada': True},
             {'nombre': 'Bass Gear Magazine',
              'url': 'https://www.bassgearmag.com/feed/',
              'instrumentos': ['bajo'],
              'especializada': True},
             {'nombre': 'For Bass Players Only',
              'url': 'https://forbassplayersonly.com/feed/',
              'instrumentos': ['bajo'],
              'especializada': True},
             {'nombre': 'TalkingBass',
              'url': 'https://www.talkingbass.net/feed/',
              'instrumentos': ['bajo'],
              'especializada': True},
             {'nombre': 'StudyBass',
              'url': 'https://www.studybass.com/feed/',
              'instrumentos': ['bajo'],
              'especializada': True},
             {'nombre': 'BassBuzz',
              'url': 'https://www.bassbuzz.com/feed/',
              'instrumentos': ['bajo'],
              'especializada': True},
             {'nombre': 'MusicRadar Bass',
              'url': 'https://www.musicradar.com/rss/news/guitars/bass-guitars',
              'instrumentos': ['bajo'],
              'especializada': True,
              'editorial': 'future'},
             {'nombre': 'Synthtopia',
              'url': 'https://www.synthtopia.com/feed/',
              'instrumentos': ['teclados'],
              'especializada': True},
             {'nombre': 'Gearnews Synth',
              'url': 'https://www.gearnews.com/zone/synth/feed/',
              'instrumentos': ['teclados'],
              'especializada': True,
              'editorial': 'gearnews'},
             {'nombre': 'Synth Anatomy',
              'url': 'https://synthanatomy.com/feed/atom',
              'instrumentos': ['teclados'],
              'especializada': True},
             {'nombre': 'CDM',
              'url': 'https://cdm.link/feed/',
              'instrumentos': ['teclados', 'proaudio']},
             {'nombre': 'Hispasonic',
              'url': 'https://www.hispasonic.com/rss',
              'idioma': 'es',
              'instrumentos': ['teclados', 'proaudio', 'bateria'],
              'activa': False},
             {'nombre': 'Modern Drummer',
              'url': 'https://www.moderndrummer.com/category/news-and-events/feed/',
              'instrumentos': ['bateria'],
              'especializada': True},
             {'nombre': 'Gearnews Drums',
              'url': 'https://www.gearnews.com/zone/drums/feed/',
              'instrumentos': ['bateria'],
              'especializada': True,
              'editorial': 'gearnews'},
             {'nombre': 'Drum Shop UK',
              'url': 'https://www.drumshop.co.uk/blogs/news.atom',
              'instrumentos': ['bateria'],
              'especializada': True},
             {'nombre': 'Drummerszone',
              'url': 'https://drummerszone.com/rss',
              'instrumentos': ['bateria'],
              'especializada': True,
              'activa': False},
             {'nombre': 'Digital Drummer',
              'url': 'https://digitaldrummermag.com/feed/',
              'instrumentos': ['bateria'],
              'especializada': True,
              'activa': False},
             {'nombre': 'ProSoundWeb',
              'url': 'https://www.prosoundweb.com/feed/',
              'instrumentos': ['proaudio'],
              'especializada': True},
             {'nombre': 'Mix',
              'url': 'https://www.mixonline.com/feed',
              'instrumentos': ['proaudio'],
              'especializada': True,
              'editorial': 'future'},
             {'nombre': 'Sound On Sound',
              'url': 'https://www.soundonsound.com/news/rss',
              'instrumentos': ['proaudio', 'teclados']},
             {'nombre': 'Recording Magazine',
              'url': 'https://www.recordingmag.com/feed/',
              'instrumentos': ['proaudio'],
              'especializada': True},
             {'nombre': 'audioXpress',
              'url': 'https://audioxpress.com/rss',
              'instrumentos': ['proaudio'],
              'especializada': True},
             {'nombre': 'Gearnews Studio',
              'url': 'https://www.gearnews.com/zone/studio/feed/',
              'instrumentos': ['proaudio'],
              'especializada': True,
              'editorial': 'gearnews'},
             {'nombre': 'Panorama Audiovisual',
              'url': 'https://www.panoramaaudiovisual.com/category/audio/feed/',
              'idioma': 'es',
              'instrumentos': ['proaudio'],
              'especializada': True}]}


if __name__ == "__main__":
    sys.exit(main())
