/* See LICENSE file for copyright and license details.
 *
 * To understand surf, start reading main().
 */

#include <signal.h>
#include <X11/X.h>
#include <X11/Xatom.h>
#include <gtk/gtk.h>
#include <gdk/gdkx.h>
#include <gdk/gdk.h>
#include <gdk/gdkkeysyms.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#include <limits.h>
#include <stdlib.h>
#include <stdio.h>
#include <webkit/webkit.h>
#include <glib/gstdio.h>
#include <JavaScriptCore/JavaScript.h>
#include <sys/file.h>
#include <libgen.h>
#include <stdarg.h>
#include <regex.h>

#include "arg.h"

char *argv0;

#define LENGTH(x)               (sizeof x / sizeof x[0])
#define CLEANMASK(mask)         (mask & (MODKEY|GDK_SHIFT_MASK))
#define COOKIEJAR_TYPE          (cookiejar_get_type ())
#define COOKIEJAR(obj)          (G_TYPE_CHECK_INSTANCE_CAST ((obj), COOKIEJAR_TYPE, CookieJar))

enum { AtomFind, AtomGo, AtomUri, AtomLast };
enum {
	ClkDoc   = WEBKIT_HIT_TEST_RESULT_CONTEXT_DOCUMENT,
	ClkLink  = WEBKIT_HIT_TEST_RESULT_CONTEXT_LINK,
	ClkImg   = WEBKIT_HIT_TEST_RESULT_CONTEXT_IMAGE,
	ClkMedia = WEBKIT_HIT_TEST_RESULT_CONTEXT_MEDIA,
	ClkSel   = WEBKIT_HIT_TEST_RESULT_CONTEXT_SELECTION,
	ClkEdit  = WEBKIT_HIT_TEST_RESULT_CONTEXT_EDITABLE,
	ClkAny   = ClkDoc | ClkLink | ClkImg | ClkMedia | ClkSel | ClkEdit,
};

typedef union Arg Arg;
union Arg {
	gboolean b;
	gint i;
	const void *v;
};

typedef struct Client {
	GtkWidget *win, *scroll, *vbox, *pane;
	WebKitWebView *view;
	WebKitWebInspector *inspector;
	char *title, *linkhover;
	const char *needle;
	gint progress;
	struct Client *next;
	gboolean zoomed, fullscreen, isinspecting, sslfailed;
} Client;

typedef struct {
	guint mod;
	guint keyval;
	void (*func)(Client *c, const Arg *arg);
	const Arg arg;
} Key;

typedef struct {
	unsigned int click;
	unsigned int mask;
	guint button;
	void (*func)(Client *c, const Arg *arg);
	const Arg arg;
} Button;

typedef struct {
	SoupCookieJarText parent_instance;
	int lock;
} CookieJar;

typedef struct {
	SoupCookieJarTextClass parent_class;
} CookieJarClass;

G_DEFINE_TYPE(CookieJar, cookiejar, SOUP_TYPE_COOKIE_JAR_TEXT)

typedef struct {
	char *regex;
	char *style;
	regex_t re;
} SiteStyle;

static Display *dpy;
static Atom atoms[AtomLast];
static Client *clients = NULL;
static GdkNativeWindow embed = 0;
static gboolean showxid = FALSE;
static char winid[64];
static gboolean usingproxy = 0;
static char togglestat[10];
static char pagestat[3];
static GTlsDatabase *tlsdb;
static int policysel = 0;
static char *stylefile = NULL;
static char *origin_uri = NULL;
static char *referring_origin = NULL;
static SoupCache *diskcache = NULL;
static gboolean hasloaded = false;
static gboolean hasvisual = false;

static void acceptlanguagescramble();
static void addaccelgroup(Client *c);
static void beforerequest(WebKitWebView *w, WebKitWebFrame *f,
		WebKitWebResource *r, WebKitNetworkRequest *req,
		WebKitNetworkResponse *resp, Client *c);
static char *buildpath(const char *path);
static gboolean buttonrelease(WebKitWebView *web, GdkEventButton *e, Client *c);
static void cleanup(void);
static void clipboard(Client *c, const Arg *arg);

/* Cookiejar implementation */
static void cookiejar_changed(SoupCookieJar *self, SoupCookie *old_cookie,
		SoupCookie *new_cookie);
static void cookiejar_finalize(GObject *self);
static SoupCookieJarAcceptPolicy cookiepolicy_get(void);
static SoupCookieJar *cookiejar_new(const char *filename, gboolean read_only,
		SoupCookieJarAcceptPolicy policy);
static void cookiejar_set_property(GObject *self, guint prop_id,
		const GValue *value, GParamSpec *pspec);
static char cookiepolicy_set(const SoupCookieJarAcceptPolicy p);

static char *copystr(char **str, const char *src);
static WebKitWebView *createwindow(WebKitWebView *v, WebKitWebFrame *f,
		Client *c);
static gboolean decidedownload(WebKitWebView *v, WebKitWebFrame *f,
		WebKitNetworkRequest *r, gchar *m,  WebKitWebPolicyDecision *p,
		Client *c);
static gboolean decidenavigation(WebKitWebView *v, WebKitWebFrame *f,
		WebKitNetworkRequest *r, WebKitWebNavigationAction *n,
		WebKitWebPolicyDecision *p, Client *c);
static gboolean decidewindow(WebKitWebView *v, WebKitWebFrame *f,
		WebKitNetworkRequest *r, WebKitWebNavigationAction *n,
		WebKitWebPolicyDecision *p, Client *c);
static gboolean deletion_interface(WebKitWebView *view,
		WebKitDOMHTMLElement *arg1, Client *c);
static void destroyclient(Client *c);
static void destroywin(GtkWidget* w, Client *c);
static void die(const char *errstr, ...);
static void eval(Client *c, const Arg *arg);
static void find(Client *c, const Arg *arg);
static void fullscreen(Client *c, const Arg *arg);
static void geopolicyrequested(WebKitWebView *v, WebKitWebFrame *f,
		WebKitGeolocationPolicyDecision *d, Client *c);
static const char *getatom(Client *c, int a);
static void gettogglestat(Client *c);
static void getpagestat(Client *c);
static char *geturi(Client *c);
static gchar *getstyle(const char *uri);

static void handleplumb(Client *c, WebKitWebView *w, const gchar *uri);

static gboolean initdownload(WebKitWebView *v, WebKitDownload *o, Client *c);

static void inspector(Client *c, const Arg *arg);
static WebKitWebView *inspector_new(WebKitWebInspector *i, WebKitWebView *v,
		Client *c);
static gboolean inspector_show(WebKitWebInspector *i, Client *c);
static gboolean inspector_close(WebKitWebInspector *i, Client *c);
static void inspector_finished(WebKitWebInspector *i, Client *c);

static gboolean keypress(GtkAccelGroup *group,
		GObject *obj, guint key, GdkModifierType mods,
		Client *c);
static void linkhover(WebKitWebView *v, const char* t, const char* l,
		Client *c);
static void loadstatuschange(WebKitWebView *view, GParamSpec *pspec,
		Client *c);
static void loaduri(Client *c, const Arg *arg, gboolean explicitnavigation);
static void navigate(Client *c, const Arg *arg);
static Client *newclient(void);
static void newwindow(Client *c, const Arg *arg, gboolean noembed, gboolean explicitnavigation);
static int origincmp(const char *uri1, const char *uri2);
static int originhas(const char *uri);
static const char *origingetproto(const char *uri);
static char *origingetfolder(const char *uri);
static char *origingethost(const char *uri);
static char *origingeturi(const char *uri);
static int originmatch(const char *uri1, const char *uri2);
static void pasteuri(GtkClipboard *clipboard, const char *text, gpointer d);
static gboolean contextmenu(WebKitWebView *view, GtkWidget *menu,
		WebKitHitTestResult *target, gboolean keyboard, Client *c);
static void menuactivate(GtkMenuItem *item, Client *c);
static void print(Client *c, const Arg *arg);
static GdkFilterReturn processx(GdkXEvent *xevent, GdkEvent *event,
		gpointer d);
static void progresschange(WebKitWebView *view, GParamSpec *pspec, Client *c);
static void linkopen(Client *c, const Arg *arg);
static void linkopenembed(Client *c, const Arg *arg);
static void reload(Client *c, const Arg *arg);
static void scroll_h(Client *c, const Arg *arg);
static void scroll_v(Client *c, const Arg *arg);
static void scroll(GtkAdjustment *a, const Arg *arg);
static void setatom(Client *c, int a, const char *v);
static void setup(const char *uri_arg);
static void sigchld(int unused);
static void source(Client *c, const Arg *arg);
static void spawn(Client *c, const Arg *arg);
static gchar *strentropy();
static gchar *strlangentropy();
static int strrand(char *buf, int buflen);
static void stop(Client *c, const Arg *arg);
static void useragentscramble(WebKitWebView *view);
static void titlechange(WebKitWebView *view, GParamSpec *pspec, Client *c);
static void titlechangeleave(void *a, void *b, Client *c);
static void toggle(Client *c, const Arg *arg);
static void togglecookiepolicy(Client *c, const Arg *arg);
static void togglegeolocation(Client *c, const Arg *arg);
static void togglescrollbars(Client *c, const Arg *arg);
static void togglestyle(Client *c, const Arg *arg);
static void updatetitle(Client *c);
static void updatewinid(Client *c);
static void usage(void);
char *qualify_uri(const char *uri);
static void windowobjectcleared(GtkWidget *w, WebKitWebFrame *frame,
		JSContextRef js, JSObjectRef win, Client *c);
static void zoom(Client *c, const Arg *arg);

/* configuration, allows nested code to access above variables */
#include "config.h"

static void
addaccelgroup(Client *c) {
	int i;
	GtkAccelGroup *group = gtk_accel_group_new();
	GClosure *closure;

	for(i = 0; i < LENGTH(keys); i++) {
		closure = g_cclosure_new(G_CALLBACK(keypress), c, NULL);
		gtk_accel_group_connect(group, keys[i].keyval, keys[i].mod,
				0, closure);
	}
	gtk_window_add_accel_group(GTK_WINDOW(c->win), group);
}

static void
beforerequest(WebKitWebView *w, WebKitWebFrame *f, WebKitWebResource *r,
		WebKitNetworkRequest *req, WebKitNetworkResponse *resp,
		Client *c) {
	const gchar *uri = webkit_network_request_get_uri(req);
	int i, isascii = 1;

	if(g_str_has_suffix(uri, "/favicon.ico"))
		webkit_network_request_set_uri(req, "about:blank");

	if(!g_str_has_prefix(uri, "http://") \
			&& !g_str_has_prefix(uri, "https://") \
			&& !g_str_has_prefix(uri, "about:") \
			&& !g_str_has_prefix(uri, "file://") \
			&& !g_str_has_prefix(uri, "data:") \
			&& !g_str_has_prefix(uri, "blob:") \
			&& strlen(uri) > 0) {

		for(i = 0; i < strlen(uri); i++) {
			if(!g_ascii_isprint(uri[i])) {
				isascii = 0;
				break;
			}
		}
		if(isascii)
			handleplumb(c, w, uri);
	}
}

static char *
buildpath(const char *path) {
	char *apath, *p;
	FILE *f;

	/* creating directory */
	if(path[0] == '/') {
		apath = g_strdup(path);
	} else if(path[0] == '~') {
		if(path[1] == '/') {
			apath = g_strconcat(g_get_home_dir(), &path[1], NULL);
		} else {
			apath = g_strconcat(g_get_home_dir(), "/",
					&path[1], NULL);
		}
	} else {
		apath = g_strconcat(g_get_current_dir(), "/", path, NULL);
	}

	if((p = strrchr(apath, '/'))) {
		*p = '\0';
		g_mkdir_with_parents(apath, 0700);
		g_chmod(apath, 0700); /* in case it existed */
		*p = '/';
	}
	/* creating file (gives error when apath ends with "/") */
	if((f = fopen(apath, "a"))) {
		g_chmod(apath, 0600); /* always */
		fclose(f);
	}

	return apath;
}

static gboolean
buttonrelease(WebKitWebView *web, GdkEventButton *e, Client *c) {
	WebKitHitTestResultContext context;
	WebKitHitTestResult *result = webkit_web_view_get_hit_test_result(web,
			e);
	Arg arg;
	unsigned int i;

	g_object_get(result, "context", &context, NULL);
	g_object_get(result, "link-uri", &arg.v, NULL);
	for(i = 0; i < LENGTH(buttons); i++) {
		if(context & buttons[i].click && e->button == buttons[i].button &&
		CLEANMASK(e->state) == CLEANMASK(buttons[i].mask) && buttons[i].func) {
			buttons[i].func(c, buttons[i].click == ClkLink && buttons[i].arg.i == 0 ? &arg : &buttons[i].arg);
			return true;
		}
	}
	return false;
}

static void
cleanup(void) {
	if(diskcache) {
		soup_cache_flush(diskcache);
		soup_cache_dump(diskcache);
	}
	while(clients)
		destroyclient(clients);
	g_free(cookiefile);
	g_free(scriptfile);
	g_free(stylefile);
}

static void
cookiejar_changed(SoupCookieJar *self, SoupCookie *old_cookie,
		SoupCookie *new_cookie) {
	flock(COOKIEJAR(self)->lock, LOCK_EX);
	if(new_cookie && !new_cookie->expires && sessiontime) {
		soup_cookie_set_expires(new_cookie,
				soup_date_new_from_now(sessiontime));
	}
	SOUP_COOKIE_JAR_CLASS(cookiejar_parent_class)->changed(self,
			old_cookie, new_cookie);
	flock(COOKIEJAR(self)->lock, LOCK_UN);
}

static void
cookiejar_class_init(CookieJarClass *klass) {
	SOUP_COOKIE_JAR_CLASS(klass)->changed = cookiejar_changed;
	G_OBJECT_CLASS(klass)->get_property =
		G_OBJECT_CLASS(cookiejar_parent_class)->get_property;
	G_OBJECT_CLASS(klass)->set_property = cookiejar_set_property;
	G_OBJECT_CLASS(klass)->finalize = cookiejar_finalize;
	g_object_class_override_property(G_OBJECT_CLASS(klass), 1, "filename");
}

static void
cookiejar_finalize(GObject *self) {
	close(COOKIEJAR(self)->lock);
	G_OBJECT_CLASS(cookiejar_parent_class)->finalize(self);
}

static void
cookiejar_init(CookieJar *self) {
	self->lock = open(cookiefile, 0);
}

static SoupCookieJar *
cookiejar_new(const char *filename, gboolean read_only,
		SoupCookieJarAcceptPolicy policy) {
	return g_object_new(COOKIEJAR_TYPE,
	                    SOUP_COOKIE_JAR_TEXT_FILENAME, filename,
	                    SOUP_COOKIE_JAR_READ_ONLY, read_only,
			    SOUP_COOKIE_JAR_ACCEPT_POLICY, policy, NULL);
}

static void
cookiejar_set_property(GObject *self, guint prop_id, const GValue *value,
		GParamSpec *pspec) {
	flock(COOKIEJAR(self)->lock, LOCK_SH);
	G_OBJECT_CLASS(cookiejar_parent_class)->set_property(self, prop_id,
			value, pspec);
	flock(COOKIEJAR(self)->lock, LOCK_UN);
}

static SoupCookieJarAcceptPolicy
cookiepolicy_get(void) {
	switch(cookiepolicies[policysel]) {
	case 'a':
		return SOUP_COOKIE_JAR_ACCEPT_NEVER;
	case '@':
		return SOUP_COOKIE_JAR_ACCEPT_NO_THIRD_PARTY;
	case 'A':
	default:
		break;
	}

	return SOUP_COOKIE_JAR_ACCEPT_ALWAYS;
}

static char
cookiepolicy_set(const SoupCookieJarAcceptPolicy ep) {
	switch(ep) {
	case SOUP_COOKIE_JAR_ACCEPT_NEVER:
		return 'a';
	case SOUP_COOKIE_JAR_ACCEPT_NO_THIRD_PARTY:
		return '@';
	case SOUP_COOKIE_JAR_ACCEPT_ALWAYS:
	default:
		break;
	}

	return 'A';
}

static void
evalscript(JSContextRef js, char *script, char* scriptname) {
	JSStringRef jsscript, jsscriptname;
	JSValueRef exception = NULL;

	jsscript = JSStringCreateWithUTF8CString(script);
	jsscriptname = JSStringCreateWithUTF8CString(scriptname);
	JSEvaluateScript(js, jsscript, JSContextGetGlobalObject(js),
			jsscriptname, 0, &exception);
	JSStringRelease(jsscript);
	JSStringRelease(jsscriptname);
}

static void
runscript(WebKitWebFrame *frame) {
	char *script;
	GError *error;

	if(g_file_get_contents(scriptfile, &script, NULL, &error)) {
		evalscript(webkit_web_frame_get_global_context(frame),
				script, scriptfile);
	}
}

static void
clipboard(Client *c, const Arg *arg) {
	gboolean paste = *(gboolean *)arg;

	if(paste) {
		gtk_clipboard_request_text(
				gtk_clipboard_get(GDK_SELECTION_PRIMARY),
				pasteuri, c);
	} else {
		gtk_clipboard_set_text(
				gtk_clipboard_get(GDK_SELECTION_PRIMARY),
				c->linkhover ? c->linkhover : geturi(c), -1);
	}
}

static char *
copystr(char **str, const char *src) {
	char *tmp;
	tmp = g_strdup(src);

	if(str && *str) {
		g_free(*str);
		*str = tmp;
	}
	return tmp;
}

static WebKitWebView *
createwindow(WebKitWebView  *v, WebKitWebFrame *f, Client *c) {
	Client *n = newclient();
	return n->view;
}

static gboolean
decidedownload(WebKitWebView *v, WebKitWebFrame *f, WebKitNetworkRequest *r,
		gchar *m,  WebKitWebPolicyDecision *p, Client *c) {
	if(!webkit_web_view_can_show_mime_type(v, m) && !webkit_web_frame_get_parent(f)) {
		webkit_web_policy_decision_download(p);
		return TRUE;
	}
	return FALSE;
}

static gboolean
decidenavigation(WebKitWebView *view, WebKitWebFrame *f, WebKitNetworkRequest *r,
		WebKitWebNavigationAction *n, WebKitWebPolicyDecision *p,
		Client *c) {
	const char *uri = webkit_network_request_get_uri(r);
	Arg arg;

	if (!useragent) {
		useragentscramble(view);
	}
	acceptlanguagescramble();

	if (!sameoriginpolicy) {
		/* configured to not bother isolating origins */
		return FALSE;
	} else if (webkit_web_frame_get_parent(f)) {
		/* has a parent, and therefore not an origin */
		return FALSE;
	/* branches below operate on the origin, top-most frame */
	} else if (uri && (uri[0] == '\0' || strcmp(uri, "about:blank") == 0)) {
		/* nothing is really going to load */
		return FALSE;
	} else if (!hasloaded) {
		/* we *are* the new window */
		return FALSE;
	} else if (!origin_uri || originmatch(uri, origin_uri)) {
		/* origin matches */
		return FALSE;
	} else {
		/* top-most frame, and origin differs -- isolate within a new process */
		webkit_web_policy_decision_ignore(p);
		arg.v = (void *) uri;
		newwindow(NULL, &arg, 0, 0);
		return TRUE;
	}
}

static gboolean
decidewindow(WebKitWebView *view, WebKitWebFrame *f, WebKitNetworkRequest *r,
		WebKitWebNavigationAction *n, WebKitWebPolicyDecision *p,
		Client *c) {
	Arg arg;

	if(webkit_web_navigation_action_get_reason(n) ==
			WEBKIT_WEB_NAVIGATION_REASON_LINK_CLICKED) {
		webkit_web_policy_decision_ignore(p);
		arg.v = (void *)webkit_network_request_get_uri(r);
		newwindow(NULL, &arg, 0, 0);
		return TRUE;
	}
	return FALSE;
}

static gboolean
deletion_interface(WebKitWebView *view,
		WebKitDOMHTMLElement *arg1, Client *c) {
	return FALSE;
}

static void
destroyclient(Client *c) {
	Client *p;

	webkit_web_view_stop_loading(c->view);
	gtk_widget_destroy(GTK_WIDGET(c->view));
	gtk_widget_destroy(c->scroll);
	gtk_widget_destroy(c->vbox);
	gtk_widget_destroy(c->win);

	for(p = clients; p && p->next != c; p = p->next);
	if(p) {
		p->next = c->next;
	} else {
		clients = c->next;
	}
	free(c);
	if(clients == NULL)
		gtk_main_quit();
}

static void
destroywin(GtkWidget* w, Client *c) {
	destroyclient(c);
}

static void
die(const char *errstr, ...) {
	va_list ap;

	va_start(ap, errstr);
	vfprintf(stderr, errstr, ap);
	va_end(ap);
	exit(EXIT_FAILURE);
}

static void
find(Client *c, const Arg *arg) {
	const char *s;

	s = getatom(c, AtomFind);
	gboolean forward = *(gboolean *)arg;
	webkit_web_view_search_text(c->view, s, FALSE, forward, TRUE);
}

static void
fullscreen(Client *c, const Arg *arg) {
	if(c->fullscreen) {
		gtk_window_unfullscreen(GTK_WINDOW(c->win));
	} else {
		gtk_window_fullscreen(GTK_WINDOW(c->win));
	}
	c->fullscreen = !c->fullscreen;
}

static void
geopolicyrequested(WebKitWebView *v, WebKitWebFrame *f,
		WebKitGeolocationPolicyDecision *d, Client *c) {
	if(allowgeolocation) {
		webkit_geolocation_policy_allow(d);
	} else {
		webkit_geolocation_policy_deny(d);
	}
}

static const char *
getatom(Client *c, int a) {
	static char buf[BUFSIZ];
	Atom adummy;
	int idummy;
	unsigned long ldummy;
	unsigned char *p = NULL;

	XGetWindowProperty(dpy, GDK_WINDOW_XID(GTK_WIDGET(c->win)->window),
			atoms[a], 0L, BUFSIZ, False, XA_STRING,
			&adummy, &idummy, &ldummy, &ldummy, &p);
	if(p) {
		strncpy(buf, (char *)p, LENGTH(buf)-1);
	} else {
		buf[0] = '\0';
	}
	XFree(p);

	return buf;
}

static char *
geturi(Client *c) {
	char *uri;

	if(!(uri = (char *)webkit_web_view_get_uri(c->view)))
		uri = "";
	return uri;
}

static gchar *
getstyle(const char *uri) {
	int i;

	if(stylefile != NULL)
		return g_strconcat("file://", stylefile, NULL);

	for(i = 0; i < LENGTH(styles); i++) {
		if(styles[i].regex && !regexec(&(styles[i].re), uri, 0,
					NULL, 0)) {
			return g_strconcat("file://", styles[i].style, NULL);
		}
	}
	return g_strdup("");
}

static void
handleplumb(Client *c, WebKitWebView *w, const gchar *uri) {
	Arg arg;

	webkit_web_view_stop_loading(w);
	arg = (Arg)PLUMB((char *)uri);
	spawn(c, &arg);
}

static gboolean
initdownload(WebKitWebView *view, WebKitDownload *o, Client *c) {
	Arg arg;

	updatewinid(c);
	arg = (Arg)DOWNLOAD((char *)webkit_download_get_uri(o), geturi(c));
	spawn(c, &arg);
	return FALSE;
}

static void
inspector(Client *c, const Arg *arg) {
	if(c->isinspecting) {
		webkit_web_inspector_close(c->inspector);
	} else {
		webkit_web_inspector_show(c->inspector);
	}
}

static WebKitWebView *
inspector_new(WebKitWebInspector *i, WebKitWebView *v, Client *c) {
	return WEBKIT_WEB_VIEW(webkit_web_view_new());
}

static gboolean
inspector_show(WebKitWebInspector *i, Client *c) {
	WebKitWebView *w;

	if(c->isinspecting)
		return false;

	w = webkit_web_inspector_get_web_view(i);
	gtk_paned_pack2(GTK_PANED(c->pane), GTK_WIDGET(w), TRUE, TRUE);
	gtk_widget_show(GTK_WIDGET(w));
	c->isinspecting = true;

	return true;
}

static gboolean
inspector_close(WebKitWebInspector *i, Client *c) {
	GtkWidget *w;

	if(!c->isinspecting)
		return false;

	w = GTK_WIDGET(webkit_web_inspector_get_web_view(i));
	gtk_widget_hide(w);
	gtk_widget_destroy(w);
	c->isinspecting = false;

	return true;
}

static void
inspector_finished(WebKitWebInspector *i, Client *c) {
	g_free(c->inspector);
}

static gboolean
keypress(GtkAccelGroup *group, GObject *obj,
		guint key, GdkModifierType mods, Client *c) {
	guint i;
	gboolean processed = FALSE;

	mods = CLEANMASK(mods);
	key = gdk_keyval_to_lower(key);
	updatewinid(c);
	for(i = 0; i < LENGTH(keys); i++) {
		if(key == keys[i].keyval
				&& mods == keys[i].mod
				&& keys[i].func) {
			keys[i].func(c, &(keys[i].arg));
			processed = TRUE;
		}
	}

	return processed;
}

static void
linkhover(WebKitWebView *v, const char* t, const char* l, Client *c) {
	if(l) {
		c->linkhover = copystr(&c->linkhover, l);
	} else if(c->linkhover) {
		free(c->linkhover);
		c->linkhover = NULL;
	}
	updatetitle(c);
}

static void
loadstatuschange(WebKitWebView *view, GParamSpec *pspec, Client *c) {
	WebKitWebFrame *frame;
	WebKitWebDataSource *src;
	WebKitNetworkRequest *request;
	WebKitWebSettings *set = webkit_web_view_get_settings(c->view);
	SoupMessage *msg;
	char *uri;

	switch(webkit_web_view_get_load_status (c->view)) {
	case WEBKIT_LOAD_FIRST_VISUALLY_NON_EMPTY_LAYOUT:
		hasvisual = true;
		break;
	case WEBKIT_LOAD_COMMITTED:
		uri = geturi(c);
		if (strcmp(uri, "about:blank") != 0) {
			origin_uri = uri;
		}
		if(strstr(uri, "https://") == uri) {
			frame = webkit_web_view_get_main_frame(c->view);
			src = webkit_web_frame_get_data_source(frame);
			request = webkit_web_data_source_get_request(src);
			msg = webkit_network_request_get_message(request);
			c->sslfailed = !(soup_message_get_flags(msg)
			                & SOUP_MESSAGE_CERTIFICATE_TRUSTED);
		}
		setatom(c, AtomUri, uri);

		if(enablestyles) {
			g_object_set(G_OBJECT(set), "user-stylesheet-uri",
					getstyle(uri), NULL);
		}
		break;
	case WEBKIT_LOAD_FINISHED:
		c->progress = 100;
		updatetitle(c);
		if(diskcache) {
			soup_cache_flush(diskcache);
			soup_cache_dump(diskcache);
		}
		break;
	default:
		break;
	}
}

/* needs to be g_free()'d by caller */
char *
qualify_uri(const char *uri) {
	char *qualified_uri = NULL, *rp;
	struct stat st;

	/* In case it's a file path. */
	if(stat(uri, &st) == 0) {
		rp = realpath(uri, NULL);
		qualified_uri = g_strdup_printf("file://%s", rp);
		free(rp);
	} else {
		qualified_uri = g_strrstr(uri, "://") ? g_strdup(uri)
			: g_strdup_printf("http://%s", uri);
	}

	return qualified_uri;
}

static void
loaduri(Client *c, const Arg *arg, gboolean explicitnavigation) {
	const char *uri = (char *)arg->v;
	Arg a = { .b = FALSE };

	if(strcmp(uri, "") == 0)
		return;

	if (!sameoriginpolicy || !origin_uri || !originhas(origin_uri) || originmatch(uri, origin_uri)) {
		setatom(c, AtomUri, uri);

		/* prevents endless loop */
		if(strcmp(uri, geturi(c)) == 0) {
			reload(c, &a);
		} else {
			webkit_web_view_load_uri(c->view, uri);
			c->progress = 0;
			hasloaded = true;
			c->title = copystr(&c->title, uri);
			updatetitle(c);
		}
	} else {
		newwindow(NULL, arg, 0, explicitnavigation);
	}
}

static void
navigate(Client *c, const Arg *arg) {
	int steps = *(int *)arg;
	webkit_web_view_go_back_or_forward(c->view, steps);
}

static Client *
newclient(void) {
	Client *c;
	WebKitWebSettings *settings;
	WebKitWebFrame *frame;
	GdkGeometry hints = { 1, 1 };
	GdkScreen *screen;
	gdouble dpi;
	char *ua;

	if(!(c = calloc(1, sizeof(Client))))
		die("Cannot malloc!\n");

	c->title = NULL;
	c->progress = 100;
	hasloaded = false;

	/* Window */
	if(embed) {
		c->win = gtk_plug_new(embed);
	} else {
		c->win = gtk_window_new(GTK_WINDOW_TOPLEVEL);

		/* TA:  20091214:  Despite what the GNOME docs say, the ICCCM
		 * is always correct, so we should still call this function.
		 * But when doing so, we *must* differentiate between a
		 * WM_CLASS and a resource on the window.  By convention, the
		 * window class (WM_CLASS) is capped, while the resource is in
		 * lowercase.   Both these values come as a pair.
		 */
		gtk_window_set_wmclass(GTK_WINDOW(c->win), "surf", "Surf");

		/* TA:  20091214:  And set the role here as well -- so that
		 * sessions can pick this up.
		 */
		gtk_window_set_role(GTK_WINDOW(c->win), "Surf");
	}
	gtk_window_set_default_size(GTK_WINDOW(c->win), 800, 600);
	g_signal_connect(G_OBJECT(c->win),
			"destroy",
			G_CALLBACK(destroywin), c);
	g_signal_connect(G_OBJECT(c->win),
			"leave_notify_event",
			G_CALLBACK(titlechangeleave), c);

	if(!kioskmode)
		addaccelgroup(c);

	/* Pane */
	c->pane = gtk_vpaned_new();

	/* VBox */
	c->vbox = gtk_vbox_new(FALSE, 0);
	gtk_paned_pack1(GTK_PANED(c->pane), c->vbox, TRUE, TRUE);

	/* Webview */
	c->view = WEBKIT_WEB_VIEW(webkit_web_view_new());

	g_signal_connect(G_OBJECT(c->view),
			"notify::title",
			G_CALLBACK(titlechange), c);
	g_signal_connect(G_OBJECT(c->view),
			"hovering-over-link",
			G_CALLBACK(linkhover), c);
	g_signal_connect(G_OBJECT(c->view),
			"geolocation-policy-decision-requested",
			G_CALLBACK(geopolicyrequested), c);
	g_signal_connect(G_OBJECT(c->view),
			"create-web-view",
			G_CALLBACK(createwindow), c);
	g_signal_connect(G_OBJECT(c->view),
			"new-window-policy-decision-requested",
			G_CALLBACK(decidewindow), c);
	g_signal_connect(G_OBJECT(c->view),
			"navigation-policy-decision-requested",
			G_CALLBACK(decidenavigation), c);
	g_signal_connect(G_OBJECT(c->view),
			"mime-type-policy-decision-requested",
			G_CALLBACK(decidedownload), c);
	g_signal_connect(G_OBJECT(c->view),
			"window-object-cleared",
			G_CALLBACK(windowobjectcleared), c);
	g_signal_connect(G_OBJECT(c->view),
			"notify::load-status",
			G_CALLBACK(loadstatuschange), c);
	g_signal_connect(G_OBJECT(c->view),
			"notify::progress",
			G_CALLBACK(progresschange), c);
	g_signal_connect(G_OBJECT(c->view),
			"download-requested",
			G_CALLBACK(initdownload), c);
	g_signal_connect(G_OBJECT(c->view),
			"button-release-event",
			G_CALLBACK(buttonrelease), c);
	g_signal_connect(G_OBJECT(c->view),
			"context-menu",
			G_CALLBACK(contextmenu), c);
	g_signal_connect(G_OBJECT(c->view),
			"resource-request-starting",
			G_CALLBACK(beforerequest), c);
	g_signal_connect(G_OBJECT(c->view),
			"should-show-delete-interface-for-element",
			G_CALLBACK(deletion_interface), c);

	/* Scrolled Window */
	c->scroll = gtk_scrolled_window_new(NULL, NULL);

	frame = webkit_web_view_get_main_frame(WEBKIT_WEB_VIEW(c->view));
	g_signal_connect(G_OBJECT(frame), "scrollbars-policy-changed",
			G_CALLBACK(gtk_true), NULL);

	if(!enablescrollbars) {
		gtk_scrolled_window_set_policy(GTK_SCROLLED_WINDOW(c->scroll),
				GTK_POLICY_NEVER, GTK_POLICY_NEVER);
	} else {
		gtk_scrolled_window_set_policy(GTK_SCROLLED_WINDOW(c->scroll),
				GTK_POLICY_AUTOMATIC, GTK_POLICY_AUTOMATIC);
	}

	/* Arranging */
	gtk_container_add(GTK_CONTAINER(c->scroll), GTK_WIDGET(c->view));
	gtk_container_add(GTK_CONTAINER(c->win), c->pane);
	gtk_container_add(GTK_CONTAINER(c->vbox), c->scroll);

	/* Setup */
	gtk_box_set_child_packing(GTK_BOX(c->vbox), c->scroll, TRUE,
			TRUE, 0, GTK_PACK_START);
	gtk_widget_grab_focus(GTK_WIDGET(c->view));
	gtk_widget_show(c->pane);
	gtk_widget_show(c->vbox);
	gtk_widget_show(c->scroll);
	gtk_widget_show(GTK_WIDGET(c->view));
	gtk_widget_show(c->win);
	gtk_window_set_geometry_hints(GTK_WINDOW(c->win), NULL, &hints,
			GDK_HINT_MIN_SIZE);
	gdk_window_set_events(GTK_WIDGET(c->win)->window, GDK_ALL_EVENTS_MASK);
	gdk_window_add_filter(GTK_WIDGET(c->win)->window, processx, c);
	webkit_web_view_set_full_content_zoom(c->view, TRUE);

	runscript(frame);

	settings = webkit_web_view_get_settings(c->view);
	g_object_set(G_OBJECT(settings), "html5-local-storage-database-path", dbfolder, NULL);
	g_object_set(G_OBJECT(settings), "enable-running-of-insecure-content", 0, NULL);
	g_object_set(G_OBJECT(settings), "enable-offline-web-application-cache", 0, NULL);
	g_object_set(G_OBJECT(settings), "enable-dns-prefetching", 0, NULL);

	if(!(ua = getenv("SURF_USERAGENT")))
		ua = useragent;
	g_object_set(G_OBJECT(settings), "user-agent", ua, NULL);
	if (enablestyles) {
		g_object_set(G_OBJECT(settings), "user-stylesheet-uri",
					 getstyle("about:blank"), NULL);
	}
	g_object_set(G_OBJECT(settings), "auto-load-images", loadimages,
			NULL);
	g_object_set(G_OBJECT(settings), "enable-plugins", enableplugins,
			NULL);
	g_object_set(G_OBJECT(settings), "enable-scripts", enablescripts,
			NULL);
	g_object_set(G_OBJECT(settings), "enable-spatial-navigation",
			enablespatialbrowsing, NULL);
	g_object_set(G_OBJECT(settings), "enable-developer-extras",
			enableinspector, NULL);
	g_object_set(G_OBJECT(settings), "enable-default-context-menu",
			kioskmode ^ 1, NULL);
	g_object_set(G_OBJECT(settings), "default-font-size",
			defaultfontsize, NULL);
	g_object_set(G_OBJECT(settings), "resizable-text-areas",
			1, NULL);

	if (!useragent) {
		useragentscramble(c->view);
	}
	acceptlanguagescramble();

	/*
	 * While stupid, CSS specifies that a pixel represents 1/96 of an inch.
	 * This ensures websites are not unusably small with a high DPI screen.
	 * It is equivalent to firefox's "layout.css.devPixelsPerPx" setting.
	 */
	if(zoomto96dpi) {
		screen = gdk_window_get_screen(GTK_WIDGET(c->win)->window);
		dpi = gdk_screen_get_resolution(screen);
		if(dpi != -1) {
			g_object_set(G_OBJECT(settings), "enforce-96-dpi", true,
					NULL);
			webkit_web_view_set_zoom_level(c->view, dpi/96);
		}
	}
	/* This might conflict with _zoomto96dpi_. */
	if(zoomlevel != 1.0)
		webkit_web_view_set_zoom_level(c->view, zoomlevel);

	if(enableinspector) {
		c->inspector = WEBKIT_WEB_INSPECTOR(
				webkit_web_view_get_inspector(c->view));
		g_signal_connect(G_OBJECT(c->inspector), "inspect-web-view",
				G_CALLBACK(inspector_new), c);
		g_signal_connect(G_OBJECT(c->inspector), "show-window",
				G_CALLBACK(inspector_show), c);
		g_signal_connect(G_OBJECT(c->inspector), "close-window",
				G_CALLBACK(inspector_close), c);
		g_signal_connect(G_OBJECT(c->inspector), "finished",
				G_CALLBACK(inspector_finished), c);
		c->isinspecting = false;
	}

	if(runinfullscreen) {
		c->fullscreen = 0;
		fullscreen(c, NULL);
	}

	setatom(c, AtomFind, "");
	setatom(c, AtomUri, "about:blank");
	if(hidebackground)
		webkit_web_view_set_transparent(c->view, TRUE);

	c->next = clients;
	clients = c;

	if(showxid) {
		gdk_display_sync(gtk_widget_get_display(c->win));
		printf("%u\n",
			(guint)GDK_WINDOW_XID(GTK_WIDGET(c->win)->window));
		fflush(NULL);
                if (fclose(stdout) != 0) {
			die("Error closing stdout");
                }
	}

	return c;
}

static void
newwindow(Client *c, const Arg *arg, gboolean noembed, gboolean explicitnavigation) {
	guint i = 0;
	const char *cmd[22], *uri;
	const Arg a = { .v = (void *)cmd };
	char tmp[64];
	char *origin_packed = NULL;

	cmd[i++] = argv0;
	cmd[i++] = "-a";
	cmd[i++] = cookiepolicies;
	if(!enablescrollbars)
		cmd[i++] = "-b";
	if(embed && !noembed) {
		cmd[i++] = "-e";
		snprintf(tmp, LENGTH(tmp), "%u", (int)embed);
		cmd[i++] = tmp;
	}
	if(!allowgeolocation)
		cmd[i++] = "-g";
	if(!loadimages)
		cmd[i++] = "-i";
	if(kioskmode)
		cmd[i++] = "-k";
	if(!enableplugins)
		cmd[i++] = "-p";
	if(!enablescripts)
		cmd[i++] = "-s";
	if(showxid)
		cmd[i++] = "-x";
	if(sameoriginpolicy)
		cmd[i++] = "-O";
	if(enablediskcache)
		cmd[i++] = "-D";
	if(!explicitnavigation) {
		cmd[i++] = "-R";
		if (originhas(origin_uri)) {
			origin_packed = origingeturi(origin_uri);
		} else {
			origin_packed = g_strdup("-");
		}
		cmd[i++] = origin_packed;
	}
	cmd[i++] = "-c";
	cmd[i++] = cookiefile;
	cmd[i++] = "--";
	uri = arg->v ? (char *)arg->v : c->linkhover;
	if(uri)
		cmd[i++] = uri;
	cmd[i++] = NULL;
	spawn(NULL, &a);
	g_free(origin_packed);
	if (!hasvisual) {
		if(dpy)
			close(ConnectionNumber(dpy));

		exit(0);
	}
}

static gboolean
contextmenu(WebKitWebView *view, GtkWidget *menu, WebKitHitTestResult *target,
		gboolean keyboard, Client *c) {
	GList *items = gtk_container_get_children(GTK_CONTAINER(GTK_MENU(menu)));

	for(GList *l = items; l; l = l->next) {
		g_signal_connect(l->data, "activate", G_CALLBACK(menuactivate), c);
	}

	g_list_free(items);
	return FALSE;
}

static void
menuactivate(GtkMenuItem *item, Client *c) {
	/*
	 * context-menu-action-2000	open link
	 * context-menu-action-1	open link in window
	 * context-menu-action-2	download linked file
	 * context-menu-action-3	copy link location
	 * context-menu-action-7	copy image address
	 * context-menu-action-13	reload
	 * context-menu-action-10	back
	 * context-menu-action-11	forward
	 * context-menu-action-12	stop
	 */

	GtkAction *a = NULL;
	const char *name, *uri;
	GtkClipboard *prisel, *clpbrd;

	a = gtk_activatable_get_related_action(GTK_ACTIVATABLE(item));
	if(a == NULL)
		return;

	name = gtk_action_get_name(a);
	if(!g_strcmp0(name, "context-menu-action-3")) {
		prisel = gtk_clipboard_get(GDK_SELECTION_PRIMARY);
		gtk_clipboard_set_text(prisel, c->linkhover, -1);
	} else if(!g_strcmp0(name, "context-menu-action-7")) {
		prisel = gtk_clipboard_get(GDK_SELECTION_PRIMARY);
		clpbrd = gtk_clipboard_get(GDK_SELECTION_CLIPBOARD);
		uri = gtk_clipboard_wait_for_text(clpbrd);
		if(uri)
			gtk_clipboard_set_text(prisel, uri, -1);
	}
}

static int
origincmp(const char *uri1, const char *uri2) {
	/* Doesn't handle default ports, but otherwise should comply with RFC 6454, The Web Origin Concept. */
	int c;
	if        (g_str_has_prefix(uri1, "http://")  && g_str_has_prefix(uri2, "http://")) {
		return strncmp(uri1 + strlen("http://"),  uri2 + strlen("http://"),  strcspn(uri1 + strlen("http://"),  "/?#"));
	} else if (g_str_has_prefix(uri1, "https://") && g_str_has_prefix(uri2, "https://")) {
		return strncmp(uri1 + strlen("https://"), uri2 + strlen("https://"), strcspn(uri1 + strlen("https://"), "/?#"));
	} else {
		c = strcmp(uri1, uri2);
		if (c == 0) {
			/* -1 when 0 to force a mismatch in originmatch() */
			c = -1;
		}
		return c;
	}
}

static int
originhas(const char *uri) {
	char *origin = origingethost(uri);
	int has = origin != NULL;
	free(origin);
	return has;
}

static const char *
origingetproto(const char *uri) {
	if (g_str_has_prefix(uri, "http://")) {
		return "http";
	} else if (g_str_has_prefix(uri, "https://")) {
		return "https";
	} else {
		return NULL;
	}
}

/* caller must free() the return value, if not NULL */
static char *
origingethost(const char *uri) {
	/* Doesn't handle default ports, but otherwise should comply with RFC 6454, The Web Origin Concept. */
	char  *origin = NULL;
	size_t spansize;
	size_t spanstart;

	if (       g_str_has_prefix(uri, "http://")) {
		spanstart =       strlen("http://");
	} else if (g_str_has_prefix(uri, "https://")) {
		spanstart =       strlen("https://");
	} else {
		/* 
		 * RFC 6454: this case should return a globally unique origin. 
		 *
		 * As long as processes are per-origin
		 * (that is, new origins get a new process),
		 * then relying only on process state provides this uniqueness,
		 * since anything stored would be stored by an inaccessible key. 
		 *
		 * So, when the caller gets this error,
		 * it should just bypass storage altogether.
		 */
		return NULL;
	}

	spansize = strcspn(uri + spanstart, "/?#");
	if (spansize > 0 && uri[spanstart] == '.') {
		/* kill attempt to traverse into parent folder */
		return NULL;
	}
	origin = malloc(sizeof(char) * (spansize + 1));
	if (origin) {
		strncpy(origin, uri + spanstart, spansize);
		origin[spansize] = '\0';
		/* malloc()'d origin */
		return origin;
	} else {
		/* ENOMEM set by malloc() */
		return NULL;
	}
}

/* caller must g_free() the return value, if not NULL */
static char *
origingeturi(const char *uri) {
	const char *origin_proto = origingetproto(uri);
	char *origin_host = origingethost(uri);
	char *origin_packed = NULL;
	if (origin_host) {
		origin_packed = g_strdup_printf("%s://%s", origin_proto, origin_host);
	}
	g_free(origin_host);
	return origin_packed;
}

/* caller must g_free() the return value, if not NULL */
static char *
origingetfolder(const char *uri) {
	const char *origin_proto = origingetproto(uri);
	char *origin_host = origingethost(uri);
	char *origin_packed = NULL;
	if (origin_host) {
		origin_packed = g_strdup_printf("%s_%s", origin_proto, origin_host);
	}
	g_free(origin_host);
	return origin_packed;
}

static int
originmatch(const char *uri1, const char *uri2) {
	return origincmp(uri1, uri2) == 0;
}

static void
pasteuri(GtkClipboard *clipboard, const char *text, gpointer d) {
	char *qualified_uri = qualify_uri(text);
	Arg arg = {.v = qualified_uri };
	if(text != NULL)
		loaduri((Client *) d, &arg, 1);
	g_free(qualified_uri);
}

static void
print(Client *c, const Arg *arg) {
	webkit_web_frame_print(webkit_web_view_get_main_frame(c->view));
}

static GdkFilterReturn
processx(GdkXEvent *e, GdkEvent *event, gpointer d) {
	Client *c = (Client *)d;
	XPropertyEvent *ev;
	Arg arg;
	const char *unqualified_uri = NULL;
	char *qualified_uri = NULL;

	if(((XEvent *)e)->type == PropertyNotify) {
		ev = &((XEvent *)e)->xproperty;
		if(ev->state == PropertyNewValue) {
			if(ev->atom == atoms[AtomFind]) {
				arg.b = TRUE;
				find(c, &arg);

				return GDK_FILTER_REMOVE;
			} else if(ev->atom == atoms[AtomGo]) {
				unqualified_uri = getatom(c, AtomGo);
				if (unqualified_uri) {
					qualified_uri = qualify_uri(unqualified_uri);
					if (qualified_uri) {
						arg.v = qualified_uri;
						loaduri(c, &arg, 1);
						g_free(qualified_uri);
	
						return GDK_FILTER_REMOVE;
					}
				}
			}
		}
	}
	return GDK_FILTER_CONTINUE;
}

static void
progresschange(WebKitWebView *view, GParamSpec *pspec, Client *c) {
	c->progress = webkit_web_view_get_progress(c->view) * 100;
	updatetitle(c);
}

static void
linkopen(Client *c, const Arg *arg) {
	newwindow(NULL, arg, 1, 0);
}

static void
linkopenembed(Client *c, const Arg *arg) {
	newwindow(NULL, arg, 0, 0);
}

static void
reload(Client *c, const Arg *arg) {
	gboolean nocache = *(gboolean *)arg;
	if(nocache) {
		 webkit_web_view_reload_bypass_cache(c->view);
	} else {
		 webkit_web_view_reload(c->view);
	}
}

static void
scroll_h(Client *c, const Arg *arg) {
	scroll(gtk_scrolled_window_get_hadjustment(
				GTK_SCROLLED_WINDOW(c->scroll)), arg);
}

static void
scroll_v(Client *c, const Arg *arg) {
	scroll(gtk_scrolled_window_get_vadjustment(
				GTK_SCROLLED_WINDOW(c->scroll)), arg);
}

static void
scroll(GtkAdjustment *a, const Arg *arg) {
	gdouble v;

	v = gtk_adjustment_get_value(a);
	switch(arg->i) {
	case +10000:
	case -10000:
		v += gtk_adjustment_get_page_increment(a) *
			(arg->i / 10000);
		break;
	case +20000:
	case -20000:
	default:
		v += gtk_adjustment_get_step_increment(a) * arg->i;
	}

	v = MAX(v, 0.0);
	v = MIN(v, gtk_adjustment_get_upper(a) -
			gtk_adjustment_get_page_size(a));
	gtk_adjustment_set_value(a, v);
}

static void
setatom(Client *c, int a, const char *v) {
	XSync(dpy, False);
	XChangeProperty(dpy, GDK_WINDOW_XID(GTK_WIDGET(c->win)->window),
			atoms[a], XA_STRING, 8, PropModeReplace,
			(unsigned char *)v, strlen(v) + 1);
	XSync(dpy, False);
}

static void
setup(const char *qualified_uri) {
	int i;
	char *proxy;
	char *new_proxy;
	char *origin;
	char *originpath;
	SoupURI *puri;
	SoupSession *s;
	GError *error = NULL;

	/* clean up any zombies immediately */
	sigchld(0);
	gtk_init(NULL, NULL);

	dpy = GDK_DISPLAY();

	/* atoms */
	atoms[AtomFind] = XInternAtom(dpy, "_SURF_FIND", False);
	atoms[AtomGo] = XInternAtom(dpy, "_SURF_GO", False);
	atoms[AtomUri] = XInternAtom(dpy, "_SURF_URI", False);

	/* dirs and files */
	if (sameoriginpolicy && qualified_uri && originhas(qualified_uri)) {
		origin = origingetfolder(qualified_uri);

		originpath = g_strdup_printf(origincookiefile, origin);
		cookiefile = buildpath(originpath);
		g_free(originpath);

		originpath = g_strdup_printf(origincachefolder, origin);
		cachefolder = buildpath(originpath);
		g_free(originpath);

		originpath = g_strdup_printf(origindbfolder, origin);
		dbfolder = buildpath(originpath);
		g_free(originpath);

		free(origin);
	} else {
		cookiefile = buildpath(cookiefile);
		cachefolder = buildpath(cachefolder);
		dbfolder = buildpath(dbfolder);
	}

	scriptfile = buildpath(scriptfile);
	styledir = buildpath(styledir);
	if(stylefile == NULL) {
		for(i = 0; i < LENGTH(styles); i++) {
			if(regcomp(&(styles[i].re), styles[i].regex,
						REG_EXTENDED)) {
				fprintf(stderr,
					"Could not compile regex: %s\n",
					styles[i].regex);
				styles[i].regex = NULL;
			}
			styles[i].style = buildpath(
					g_strconcat(styledir,
						styles[i].style, NULL));
		}
	} else {
		stylefile = buildpath(stylefile);
	}

	/* request handler */
	s = webkit_get_default_session();

	/* cookie jar */
	soup_session_add_feature(s,
			SOUP_SESSION_FEATURE(cookiejar_new(cookiefile, FALSE,
					cookiepolicy_get())));

	/* disk cache */
	if(enablediskcache) {
		diskcache = soup_cache_new(cachefolder, SOUP_CACHE_SINGLE_USER);
		soup_cache_set_max_size(diskcache, diskcachebytes);
		soup_cache_load(diskcache);
		soup_session_add_feature(s, SOUP_SESSION_FEATURE(diskcache));
	}

	/* ssl */
	tlsdb = g_tls_file_database_new(cafile, &error);

	if(error) {
		g_warning("Error loading SSL database %s: %s", cafile, error->message);
		g_error_free(error);
	}
	g_object_set(G_OBJECT(s), "tls-database", tlsdb, NULL);
	g_object_set(G_OBJECT(s), "ssl-strict", strictssl, NULL);

	/* proxy */
	if((proxy = getenv("http_proxy")) && strcmp(proxy, "")) {
		new_proxy = g_strrstr(proxy, "http://") ? g_strdup(proxy) :
			g_strdup_printf("http://%s", proxy);
		puri = soup_uri_new(new_proxy);
		g_object_set(G_OBJECT(s), "proxy-uri", puri, NULL);
		soup_uri_free(puri);
		g_free(new_proxy);
		usingproxy = 1;
	}
}

static void
sigchld(int unused) {
	if(signal(SIGCHLD, sigchld) == SIG_ERR)
		die("Can't install SIGCHLD handler");
	while(0 < waitpid(-1, NULL, WNOHANG));
}

static void
source(Client *c, const Arg *arg) {
	Arg a = { .b = FALSE };
	gboolean s;

	s = webkit_web_view_get_view_source_mode(c->view);
	webkit_web_view_set_view_source_mode(c->view, !s);
	reload(c, &a);
}

static void
spawn(Client *c, const Arg *arg) {
	if(fork() == 0) {
		if(dpy)
			close(ConnectionNumber(dpy));
		setsid();
		execvp(((char **)arg->v)[0], (char **)arg->v);
		fprintf(stderr, "surf: execvp %s", ((char **)arg->v)[0]);
		perror(" failed");
		exit(0);
	}
}

static int
strrand(char *buf, int buflen) {
	int fd;
	int received;

	fd = g_open("/dev/urandom", O_RDONLY, 0);
	if (fd == -1) {
		return -1;
	}
	received = read(fd, buf, buflen);
	if (received != buflen) {
		return -1;
	}
	return g_close(fd, NULL);
}

/* return value must be freed with g_free() */
static gchar *
strentropy() {
	gchar *strname = NULL;
	char byte, randbuf[256], namebuf[256];
	int rand_i, name_i;

	if (strrand(randbuf, sizeof (randbuf)) == -1) {
		return NULL;
	}

	name_i = 0;
	for (rand_i = 0; rand_i < sizeof (randbuf) && name_i < sizeof (namebuf); rand_i++) {
		byte = randbuf[rand_i];
		if (byte >= ' ' - 5 && byte <= ' ') { /* space AND some characters below, to increase the number of spaces */
			namebuf[name_i++] = ' ';
		} else if ((byte >= 'A' && byte <= 'Z') || (byte >= 'a' && byte <= 'z') || (byte >= '0' && byte <= '9')) {
			namebuf[name_i++] = byte;
		} else {
			/* some bytes are skipped, to randomly vary the length */
		}
	}
	namebuf[name_i] = '\0';
	strname = g_strndup(namebuf, sizeof(namebuf) - 1);

	return strname;
}

/* return value must be freed with g_free() */
static gchar *
strlangentropy() {
	gchar *strname = NULL;
	char randbuf[4], langbuf[6];

	if (strrand(randbuf, sizeof (randbuf)) == -1) {
		return NULL;
	}

#define randbetween(low, high, randbyte) (low + ((unsigned char) randbyte % (high - low)))
	langbuf[0] = randbetween('a', 'z', randbuf[0]); 
	langbuf[1] = randbetween('a', 'z', randbuf[1]);
	langbuf[2] = '_';
	langbuf[3] = randbetween('A', 'Z', randbuf[2]);
	langbuf[4] = randbetween('A', 'Z', randbuf[3]);
	langbuf[5] = '\0';

	strname = g_strdup(langbuf);

	return strname;
}

static void
acceptlanguagescramble() {
	SoupSession *s = webkit_get_default_session();
	char *lang = getenv("LANG");
	char *randlang1 = strlangentropy();
	char *randlang2 = strlangentropy();
	char *acceptlanguage;

	if (strlen(lang) >= 5) {
		acceptlanguage = g_strdup_printf("%5.5s, %s;q=0.9, %s;q=0.8", lang, randlang1, randlang2);
		g_object_set(G_OBJECT(s), "accept-language", acceptlanguage, NULL);
	}
	g_free(randlang1);
	g_free(randlang2);
}

static void
useragentscramble(WebKitWebView *view) {
	WebKitWebSettings *settings = webkit_web_view_get_settings(view);
	gchar *ua = strentropy();
	if (!ua) 
		ua = " "; /* fallback to blank user-agent -- NULL or "" return a webkit default string that leaks information */
	g_object_set(G_OBJECT(settings), "user-agent", ua, NULL);
	g_free(ua);
}

static void
eval(Client *c, const Arg *arg) {
	WebKitWebFrame *frame = webkit_web_view_get_main_frame(c->view);
	evalscript(webkit_web_frame_get_global_context(frame),
			((char **)arg->v)[0], "");
}

static void
stop(Client *c, const Arg *arg) {
	webkit_web_view_stop_loading(c->view);
}

static void
titlechange(WebKitWebView *view, GParamSpec *pspec, Client *c) {
	const gchar *t = webkit_web_view_get_title(view);
	if (t) {
		c->title = copystr(&c->title, t);
		updatetitle(c);
	}
}

static void
titlechangeleave(void *a, void *b, Client *c) {
	c->linkhover = NULL;
	updatetitle(c);
}

static void
toggle(Client *c, const Arg *arg) {
	WebKitWebSettings *settings;
	char *name = (char *)arg->v;
	gboolean value;
	Arg a = { .b = FALSE };

	settings = webkit_web_view_get_settings(c->view);
	g_object_get(G_OBJECT(settings), name, &value, NULL);
	g_object_set(G_OBJECT(settings), name, !value, NULL);

	reload(c, &a);
}

static void
togglecookiepolicy(Client *c, const Arg *arg) {
	SoupCookieJar *jar;
	SoupCookieJarAcceptPolicy policy;

	jar = SOUP_COOKIE_JAR(
			soup_session_get_feature(
				webkit_get_default_session(),
				SOUP_TYPE_COOKIE_JAR));
	g_object_get(G_OBJECT(jar), "accept-policy", &policy, NULL);

	policysel++;
	if(policysel >= strlen(cookiepolicies))
		policysel = 0;

	g_object_set(G_OBJECT(jar), "accept-policy",
			cookiepolicy_get(), NULL);

	updatetitle(c);
	/* Do not reload. */
}

static void
togglegeolocation(Client *c, const Arg *arg) {
	Arg a = { .b = FALSE };

	allowgeolocation ^= 1;

	reload(c, &a);
}

static void
twitch(Client *c, const Arg *arg) {
	GtkAdjustment *a;
	gdouble v;

	a = gtk_scrolled_window_get_vadjustment(
			GTK_SCROLLED_WINDOW(c->scroll));

	v = gtk_adjustment_get_value(a);

	v += arg->i;

	v = MAX(v, 0.0);
	v = MIN(v, gtk_adjustment_get_upper(a) -
			gtk_adjustment_get_page_size(a));
	gtk_adjustment_set_value(a, v);
}

static void
togglescrollbars(Client *c, const Arg *arg) {
	GtkPolicyType vspolicy;
	Arg a;

	gtk_scrolled_window_get_policy(GTK_SCROLLED_WINDOW(c->scroll), NULL, &vspolicy);

	if(vspolicy == GTK_POLICY_AUTOMATIC) {
		gtk_scrolled_window_set_policy(GTK_SCROLLED_WINDOW(c->scroll),
				GTK_POLICY_NEVER, GTK_POLICY_NEVER);
	} else {
		gtk_scrolled_window_set_policy(GTK_SCROLLED_WINDOW(c->scroll),
				GTK_POLICY_AUTOMATIC, GTK_POLICY_AUTOMATIC);
		a.i = +1;
		twitch(c, &a);
		a.i = -1;
		twitch(c, &a);
	}
}

static void
togglestyle(Client *c, const Arg *arg) {
	WebKitWebSettings *settings = webkit_web_view_get_settings(c->view);
	char *uri;

	enablestyles = !enablestyles;
	uri = enablestyles ? getstyle(geturi(c)) : g_strdup("");
	g_object_set(G_OBJECT(settings), "user-stylesheet-uri", uri, NULL);

	updatetitle(c);
}

static void
gettogglestat(Client *c){
	gboolean value;
	int p = 0;
	WebKitWebSettings *settings = webkit_web_view_get_settings(c->view);

	togglestat[p++] = cookiepolicy_set(cookiepolicy_get());

	g_object_get(G_OBJECT(settings), "enable-caret-browsing",
			&value, NULL);
	togglestat[p++] = value? 'C': 'c';

	togglestat[p++] = allowgeolocation? 'G': 'g';

	togglestat[p++] = enablediskcache? 'D': 'd';

	togglestat[p++] = sameoriginpolicy? 'O' : 'o';

	g_object_get(G_OBJECT(settings), "auto-load-images", &value, NULL);
	togglestat[p++] = value? 'I': 'i';

	g_object_get(G_OBJECT(settings), "enable-scripts", &value, NULL);
	togglestat[p++] = value? 'S': 's';

	g_object_get(G_OBJECT(settings), "enable-plugins", &value, NULL);
	togglestat[p++] = value? 'V': 'v';

	togglestat[p++] = enablestyles ? 'M': 'm';

	togglestat[p] = '\0';
}

static void
getpagestat(Client *c) {
	const char *uri = geturi(c);

	if(strstr(uri, "https://") == uri) {
		pagestat[0] = c->sslfailed ? 'U' : 'T';
	} else {
		pagestat[0] = '-';
	}

	pagestat[1] = usingproxy ? 'P' : '-';
	pagestat[2] = '\0';

}

static void
updatetitle(Client *c) {
	char *t;
	char *originstat;

	if(originhas(origin_uri)) {
		originstat = origingethost(origin_uri);
	} else {
		originstat = g_strdup("-");
	}
			

	if(showindicators) {
		gettogglestat(c);
		getpagestat(c);

		if(c->linkhover) {
			t = g_strdup_printf("%s:%s | %s", togglestat,
					pagestat, c->linkhover);
		} else if(c->progress != 100) {
			t = g_strdup_printf("[%i%%] %s:%s | %s | %s", c->progress,
					togglestat, pagestat,
					originstat,
					(c->title == NULL)? "" : c->title);
		} else {
			t = g_strdup_printf(       "%s:%s | %s | %s", 
					togglestat, pagestat,
					originstat,
					(c->title == NULL)? "" : c->title);
		}

		gtk_window_set_title(GTK_WINDOW(c->win), t);
		g_free(t);
	} else {
		gtk_window_set_title(GTK_WINDOW(c->win),
				(c->title == NULL)? "" : c->title);
	}

	g_free(originstat);
}

static void
updatewinid(Client *c) {
	snprintf(winid, LENGTH(winid), "%u",
			(int)GDK_WINDOW_XID(GTK_WIDGET(c->win)->window));
}

static void
usage(void) {
	die("usage: %s [-bBfFgGiIkKnNpPsSvx]"
		" [-a cookiepolicies ] "
		" [-c cookiefile] [-e xid] [-r scriptfile]"
		" [-t stylefile] [-u useragent] [-z zoomlevel]"
		" [uri]\n", basename(argv0));
}

static void
windowobjectcleared(GtkWidget *w, WebKitWebFrame *frame, JSContextRef js,
		JSObjectRef win, Client *c) {
	runscript(frame);
}

static void
zoom(Client *c, const Arg *arg) {
	c->zoomed = TRUE;
	if(arg->i < 0) {
		/* zoom out */
		webkit_web_view_zoom_out(c->view);
	} else if(arg->i > 0) {
		/* zoom in */
		webkit_web_view_zoom_in(c->view);
	} else {
		/* reset */
		c->zoomed = FALSE;
		webkit_web_view_set_zoom_level(c->view, 1.0);
	}
}

int
main(int argc, char *argv[]) {
	Arg arg;
	Client *c;
	char *qualified_uri = NULL;
	char *prompt = NULL;

	memset(&arg, 0, sizeof(arg));

	/* command line args */
	ARGBEGIN {
	case 'a':
		cookiepolicies = EARGF(usage());
		break;
	case 'b':
		enablescrollbars = 0;
		break;
	case 'B':
		enablescrollbars = 1;
		break;
	case 'c':
		cookiefile = EARGF(usage());
		break;
	case 'd':
		enablediskcache = 0;
		break;
	case 'D':
		enablediskcache = 1;
		break;
	case 'e':
		embed = strtol(EARGF(usage()), NULL, 0);
		break;
	case 'f':
		runinfullscreen = 1;
		break;
	case 'F':
		runinfullscreen = 0;
		break;
	case 'g':
		allowgeolocation = 0;
		break;
	case 'G':
		allowgeolocation = 1;
		break;
	case 'i':
		loadimages = 0;
		break;
	case 'I':
		loadimages = 1;
		break;
	case 'k':
		kioskmode = 0;
		break;
	case 'K':
		kioskmode = 1;
		break;
	case 'm':
		enablestyles = 0;
		break;
	case 'M':
		enablestyles = 1;
		break;
	case 'n':
		enableinspector = 0;
		break;
	case 'N':
		enableinspector = 1;
		break;
	case 'o':
		sameoriginpolicy = 0;
		break;
	case 'O':
		sameoriginpolicy = 1;
		break;
	case 'p':
		enableplugins = 0;
		break;
	case 'P':
		enableplugins = 1;
		break;
	case 'r':
		scriptfile = EARGF(usage());
		break;
	case 'R':
		referring_origin = EARGF(usage());
		break;
	case 's':
		enablescripts = 0;
		break;
	case 'S':
		enablescripts = 1;
		break;
	case 't':
		stylefile = EARGF(usage());
		break;
	case 'u':
		useragent = EARGF(usage());
		break;
	case 'v':
		die("surf-"VERSION", ©2009-2014 surf engineers, "
				"see LICENSE for details\n");
	case 'x':
		showxid = TRUE;
		break;
	case 'z':
		zoomlevel = strtof(EARGF(usage()), NULL);
		break;
	default:
		usage();
	} ARGEND;
	if(argc > 0) {
		if (argv[0]) {
			qualified_uri = qualify_uri(argv[0]);
		}
	}

	setup(qualified_uri);
	c = newclient();
	updatewinid(c);
	if(qualified_uri) {
		if (originhas(qualified_uri)) {
			origin_uri = qualified_uri;
		}
		if (sameoriginpolicy && referring_origin && (strcmp(referring_origin, "-") == 0 || !originmatch(referring_origin, qualified_uri))) {
			setatom(c, AtomUri, qualified_uri);
			prompt = g_strdup_printf(PROMPT_ORIGIN, referring_origin);
			arg = (Arg)SETPROP("_SURF_URI", "_SURF_GO", prompt);
			spawn(c, &arg);
			g_free(prompt);
		} else {
			arg.v = qualified_uri;
			loaduri(clients, &arg, 0);
		}
	} else {
		updatetitle(c);
	}

	gtk_main();
	cleanup();

	g_free(qualified_uri);

	return EXIT_SUCCESS;
}

