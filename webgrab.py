#!/usr/bin/python3

# DISCLAIMER for developers
# There is many (crazy) monkey code.
# Do not repeat it at home.


from urllib.request import (
    HTTPError,
    urlopen
)
from urllib.parse import (
    urlparse,
    urlunparse
)
from lxml.html import (
    fromstring
)
from lxml.etree import (
    tostring
)
from os.path import (
    abspath,
    sep,
    splitext,
    dirname,
    exists
)
from os import (
    getcwd,
    name as os_name,
    environ,
    remove,
    rename,
    makedirs
)
from re import (
    compile
)
from collections import (
    deque
)
from traceback import (
    print_exc
)
from itertools import (
    count,
    chain
)
from six.moves.tkinter import (
    Tk,
    Scrollbar,
    VERTICAL,
    END,
    Button
)
from six.moves.tkinter_ttk import (
    Treeview
)


# IRI
# Based on:
# https://stackoverflow.com/questions/4389572/how-to-fetch-a-non-ascii-url-with-python-urlopen

non_ascii_re = compile(b"[\x80-\xFF]")


def replacer(c):
    return b"%%%02x" % ord(c.group(0))


def urlEncodeNonAscii(b):
    return non_ascii_re.sub(replacer, b)


def iriToUri(iri):
    parts = urlparse(iri)
    return urlunparse(
        part.encode("idna").decode("ascii") if i == 1 else \
            urlEncodeNonAscii(part.encode("utf-8")).decode("ascii")
        for i, part in enumerate(parts)
    )


assert iriToUri(u"http://www.a\u0131b.com/a\u0131b") == \
    "http://www.xn--ab-hpa.com/a%c4%b1b"

BAD_CHARS = "<>:\"/\\|?*"


def escape_char(char):
    return "%" + str(ord(char))


def file_name_filter(char):
    if ord(char) < 31:
        return escape_char(char)
    if char in BAD_CHARS:
        return escape_char(char)
    return char


def fix_file_name(name):
    return "".join(map(file_name_filter, name))

if os_name == "nt":
    disk_re = compile("[a-zA-Z]:")

    def fix_file_path(path_iter):
        piter = iter(path_iter)
        try:
            first = next(piter)
        except StopIteration:
            return tuple()
        if not disk_re.match(first):
            first = fix_file_name(first)
        return (first,) + tuple(map(fix_file_name, piter))
else:
    def fix_file_path(path_iter):
        return tuple(map(fix_file_name, path_iter))


class OtherSite(ValueError):

    def __init__(self, proto, site_base, suffix):
        self.proto = proto
        self.site_base = site_base
        self.suffix = suffix


class SnapshotExists(RuntimeError): pass


page_re = compile(".+\.((htm),(html))$")

REPROCESS = True


class Resourse(object):

    def __init__(self, site, url_tuple, cache_file):
        self.site = site
        self.url_tuple = url_tuple
        self.cache_file = cache_file

        if REPROCESS and self.has_snapshot():
            remove(self.cache_file)
            rename(self.snapshot_name(), self.cache_file)

    def raw(self):
        with open(self.cache_file, "rb") as f:
            raw = f.read()
        self.__dict__["raw"] = lambda : raw
        return raw

    @property
    def is_page(self):
        res = False
        url_tuple = self.url_tuple
        if len(url_tuple) == 0:
            res = True
        elif "." not in url_tuple[-1]:
            res = True
        elif page_re.match(url_tuple[-1]):
            res = True
        self.__dict__["is_page"] = res
        return res

    def as_html(self):
        html = fromstring(self.raw())
        self.__dict__["as_html"] = lambda : html
        return html

    @property
    def current_as_string(self):
        html = self.as_html()
        return tostring(html)

    def rel_cache_path(self, towards_resource):
        self_path = dirname(abspath(self.cache_file)).split(sep)
        other_path = abspath(towards_resource.cache_file).split(sep)

        result = []

        i = 0
        try:
            while self_path[i] == other_path[i]:
                i += 1
        except IndexError:
            pass

        if len(self_path) > i:
            result.extend([".."] * (len(self_path) - i))
        if i < len(other_path):
            result.extend(other_path[i:])
        if not result:
            result.append(".")
        if not result[-1]:
            result[-1] = "."

        return sep.join(result)

    def snapshot_name(self, suffix = ".back"):
        return self.cache_file + suffix

    def snapshot(self, suffix = ".back"):
        snapshot = self.snapshot_name(suffix = suffix)
        if exists(snapshot):
            raise SnapshotExists("Snapshot already exists " + snapshot)
        raw = self.raw()
        with open(snapshot, "wb") as f:
            f.write(raw)

    def has_snapshot(self, suffix = ".back"):
        snapshot = self.snapshot_name(suffix = suffix)
        return exists(snapshot)

    def html_snapshot(self, suffix = ".back"):
        snapshot = self.snapshot_name(suffix = suffix)
        if not exists(snapshot):
            raise RuntimeError("No snapshot for %s" % self)
        with open(snapshot, "rb") as f:
            raw = f.read()
        html = fromstring(raw)
        return html

    def overwrite_cache(self):
        as_str = self.current_as_string
        with open(self.cache_file, "wb") as f:
            f.write(as_str)

    def full_url(self, rel_url):
        parts = rel_url.split("/")
        if parts[0] == "":
            parts = parts[1:]
            cur_url = []
        else:
            if parts[0][-1] == ":" and parts[1] == "": # proto://...
                return rel_url

            cur_url = list(self.url_tuple)
            if cur_url[-1]:
                cur_url.pop()

        for name in parts:
            if name == ".":
                if len(cur_url) and cur_url[-1] == "":
                    cur_url.pop()
            elif name == "..":
                if not cur_url:
                    print("Skipping .. beyond root in " + rel_url)
                elif cur_url.pop() == "":
                    cur_url.pop()
            elif name == "":
                if not cur_url or cur_url[-1]:
                    cur_url.append("")
            else:
                cur_url.append(name)

        return self.site._full_url(cur_url)

    def __str__(self):
        return self.full_url(".")


SITE_DIR_PREFIX = None


class Site(object):

    sites = {}

    @classmethod
    def parse_url(cls, url):
        proto, url_path = url.split("://", 1)
        url = url_path.split("/")
        site_base = url[0]
        suffix = url[1:]
        return proto, site_base, suffix

    def __new__(cls, url, dir = None):
        key = cls.parse_url(url)[:2]
        try:
            site = cls.sites[key]
        except KeyError:
            cls.sites[key] = site = super(Site, cls).__new__(cls)
        return site

    def __init__(self, url, dir = None):
        self.proto, site_base, suffix = Site.parse_url(url)
        self.site_base = site_base
        if dir is None:
            dir = site_base
            if SITE_DIR_PREFIX is not None:
                dir = sep.join(chain(SITE_DIR_PREFIX.split(sep), [dir]))
        self.dir = tuple(abspath(dir).split(sep))
        self.prefix = tuple(suffix)
        self.url2file = {}
        self.file2desc = {}

    def __getitem__(self, rel_url):
        return self._get_by_url(self._normalize_url(rel_url))

    def _normalize_url(self, rel_url):
        parts = rel_url.split("/")

        if parts[0][-1] == ":" and parts[1] == "": # proto://
            # it's a full URL
            proto, site_base, suffix = Site.parse_url(rel_url)
            # if (proto, site_base) != (self.proto, self.site_base):
            # XXX: previous failed on HTTP and HTTPS
            if site_base != self.site_base:
                raise OtherSite(proto, site_base, suffix)
            parts = parts[3:]
            cur_url = list()
        else:
            cur_url = list(self.prefix)

        for name in parts:
            if name == ".":
                if len(cur_url) and cur_url[-1] == "":
                    cur_url.pop()
            elif name == "..":
                if cur_url.pop() == "":
                    cur_url.pop()
            elif name == "":
                if not cur_url or cur_url[-1]:
                    cur_url.append("")
            else:
                cur_url.append(name)

        return tuple(cur_url)

    def _file_by_url(self, url_tuple):
        try:
            return self.url2file[url_tuple]
        except KeyError:
            pass

        # if url_tuple[0] != self.site_base:
        #    raise RuntimeError("Other site " + self._full_url(url_tuple))
        if len(url_tuple) == 0:
            url_tuple = ("",)

        filename_list = self.dir + url_tuple

        if not filename_list[-1]:
            filename_list = filename_list[:-1] + ("index.html",)
        elif not splitext(filename_list[-1])[1]:
            # TODO: access to directory
            filename_list = filename_list + ("index.html",)

        filename = sep.join(fix_file_path(filename_list))

        self.url2file[url_tuple] = filename
        return filename

    def _full_url(self, url_tuple):
        return self.proto + "://%s/" % self.site_base + "/".join(url_tuple)

    def _get_by_url(self, url_tuple):
        filename = self._file_by_url(url_tuple)
        try:
            return self.file2desc[filename]
        except KeyError:
            if not exists(filename):
                url = self._full_url(url_tuple)
                print("Caching " + url)
                url2 = iriToUri(url)
                with urlopen(url2) as f:
                    if f.url != url2: # redirection
                        print("Redirected to: " + f.url)
                        try:
                            desc = self[f.url]
                        except OtherSite as os:
                            site = self.sites.get((os.proto, os.site_base),
                                None
                            )
                            if site is None:
                                raise
                            desc = site[f.url]
                        self.file2desc[filename] = desc
                        return desc
                    raw = f.read()
                makedirs(dirname(filename), exist_ok = True)
                with open(filename, "wb") as f:
                    f.write(raw)

            res = Resourse(self, url_tuple, filename)

            self.file2desc[filename] = res
        return res

    def __str__(self):
        return self._full_url(self.prefix)


SKIP = object()


class Tag(object):

    def __init__(self, element):
        self.element = element

    def iter_refs(self):
        el = self.element
        for a in self.attrs:
            yield el.get(a)

    def set_refs(self, vals):
        el = self.element
        for a, v in zip(self.attrs, vals):
            if v is SKIP:
                continue
            el.set(a, v)

    def set_ref(self, idx, vel):
        self.element.set(self.attrs[idx], val)

    catch = True


class TagA(Tag):

    tag = "a"
    attrs = ("href",)


class TagIMG(Tag):

    tag = "img"
    attrs = ("src",)


class TagLink(Tag):

    tag = "link"
    attrs = ("href",)

    @property
    def catch(self):
        rel = self.element.get("rel")
        return rel.lower() == "stylesheet" \
            or rel.lower() == "shortcut icon"


globs = dict(globals())

TAG_HANDLERS = {}
for n, v in globs.items():
    if isinstance(v, type) and Tag in v.__bases__:
        TAG_HANDLERS[v.tag] = v

RE_FILTERS = [
]


def iter_inc_envs():
    yield "WEBGRAB_INC"
    for i in count(0):
        yield "WEBGRAB_INC%d" % i


def to_cache(iri):
    """This function implements logical 'AND' of all filters. I.e. to catch
an IRI all inclusion filters must match and all exclusion filters must not
match. To get logical 'OR', build a composite regular expression. Ex.:

export WEBGRAB_INC=".*www\.site\.((org)|(com)).*"
"""
    for catch, re in RE_FILTERS:
        if bool(re.match(iri)) != catch:
            return False
    return True


def co_catcher(start_page, referenced_sites):
    site = Site(start_page)

    print(site)

    try:
        starting = site["."]
    except OtherSite as os:
        referenced_sites.add((os.proto, os.site_base,
            tuple(os.suffix)
        ))
        return

    # Queue of pages to process
    queue = deque([starting])

    visited = set()

    while queue:
        page = queue.popleft()

        if page.url_tuple in visited:
            continue
        visited.add(page.url_tuple)

        yield
        print("Processing " + str(page))

        has_snapshot = page.has_snapshot()
        if has_snapshot:
            tree = page.html_snapshot()
        else:
            tree = page.as_html()

        ref_errors = False

        # stack of page DOM tree traversing
        stack = [(0, tree)]

        while stack:
            yield
            depth, el = stack.pop()
            # print(" " * depth + str(el))

            # Some tags have references to other resources (pages, images,
            # files). Many of them must be downloaded and saved in a file.
            # Each reference must be redirected to the file.
            # Also, tags frequently have different formats and catch
            # conditions.
            # There is a handler class for each supported tag name. Instances
            # of that handlers hides the differences.

            tag = el.tag
            if tag in TAG_HANDLERS:
                h = TAG_HANDLERS[tag](el)

                if h.catch:
                    updated = []
                    for ref in h.iter_refs():
                        if ref is None:
                            updated.append(SKIP)
                            continue
                        print("Reference: " + ref)

                        # TODO: use urlparse

                        parts = ref.split("#")
                        base = parts[0]
                        # skip inner references, e-mail addresses
                        if not base or base.startswith("mailto:"): #
                            updated.append(SKIP)
                            continue

                        base_and_req = base.split("?", 1)
                        if len(base_and_req) > 1:
                            print("Ignoring request " + base_and_req[1])
                            base = base_and_req[0]
                            if not base:
                                # self reference
                                base = "."

                        parts = parts[1:]
                        full_base = page.full_url(base)
                        print("Full URL: " + full_base)

                        if not to_cache(full_base):
                            print("Filtered out...")
                            updated.append(SKIP)
                            continue

                        yield
                        try:
                            res = site[full_base]
                        except OtherSite as os:
                            print("Skipping other site")
                            updated.append(ref)
                            referenced_sites.add((os.proto, os.site_base,
                                tuple(os.suffix)
                            ))
                            continue
                        except HTTPError as httpe:
                            if httpe.code == 403:
                                print("Access forbidden")
                            elif httpe.code == 404:
                                print("Not found")
                            else:
                                print_exc()
                            updated.append(SKIP)
                            ref_errors = True
                            continue

                        rel_path = page.rel_cache_path(res)
                        print("rel path: " + rel_path)
                        if parts:
                            new_ref = rel_path + "#" + "#".join(parts)
                        else:
                            new_ref = rel_path

                        new_ref = new_ref.replace("%", "%25")

                        updated.append(new_ref)

                        if res.is_page:
                            queue.append(res)

                    if not has_snapshot:
                        h.set_refs(updated)

            for ch in el:
                stack.append((depth + 1, ch))

        if not has_snapshot and not ref_errors:
            page.snapshot()
            page.overwrite_cache()


class Feedback(set):

    def __init__(self, listener):
        self._l = listener

    def add(self, el):
        super(Feedback, self).add(el)
        self._l(*el)


def main():
    global SITE_DIR_PREFIX
    SITE_DIR_PREFIX = getcwd()

    misses = 2
    for inc_env in iter_inc_envs():
        inc = environ.get(inc_env, None)
        if inc is None:
            if not misses:
                break
            misses -= 1
            continue
        RE_FILTERS.append((True, compile(inc)))

    start_page = environ.get("WEBGRAB_SITE", None)
    if start_page is None:
        print("Set WEBGRAB_SITE environment variable")
        return -1

    tk = Tk()
    tk.geometry("1000x600")
    tk.columnconfigure(0, weight = 1)
    tk.columnconfigure(1, weight = 0)
    tk.rowconfigure(0, weight = 1)
    tk.rowconfigure(1, weight = 0)
    tv = Treeview(tk)
    tv.grid(row = 0, column = 0, sticky = "NESW")

    vsb = Scrollbar(tk, orient = VERTICAL)
    vsb.grid(row = 0, column = 1, sticky = "NSE")

    tv.configure(yscrollcommand = vsb.set)
    vsb.configure(command = tv.yview)

    def on_add_site(proto, base, suffix):
        tv.insert("", END,
            text = proto + "://" + base + "/" + "/".join(suffix)
        )

    referenced_sites = Feedback(on_add_site)
    catchers = [co_catcher(start_page, referenced_sites)]

    def catch_selected():
        for iid in tv.selection():
            catcher = co_catcher(tv.item(iid, "text"), referenced_sites)
            catchers.append(catcher)
            tv.delete(iid)

    bt_catch = Button(tk, text = "Catch selected", command = catch_selected)
    bt_catch.grid(row = 1, column = 0, sticky = "NWS")

    def catch_idle():
        if catchers:
            catcher = catchers[0]
            try:
                next(catcher)
            except StopIteration:
                catchers.pop(0)
        else:
            if not tv.get_children():
                tv.destroy()

        tk.after(10, catch_idle)

    tk.after_idle(catch_idle)

    tk.mainloop()

    print("Referenced sites:")
    for s in referenced_sites:
        print(s)


if __name__ == "__main__":
    exit(main() or 0)
