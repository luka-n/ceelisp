/* The author disclaims copyright to this source code. */

#include <ctype.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* -- TYPE DECLARATIONS ------------------------------------------------------ */

typedef struct sexp Sexp;

typedef Sexp *(*Primitive)(Sexp *, Sexp *);

enum sexp_type {
  SEXP_CLOSURE, SEXP_ERROR, SEXP_FLONUM, SEXP_INTEGER, SEXP_MACRO, SEXP_NIL,
  SEXP_PAIR, SEXP_PRIMITIVE, SEXP_STRING, SEXP_SYMBOL, SEXP_TRUE
};

struct sexp {
  enum sexp_type type;
  union {
    struct {
      Sexp *args;
      Sexp *body;
      Sexp *env;
    } closure;
    char *error;
    float flonum;
    int integer;
    struct {
      Sexp *args;
      Sexp *body;
    } macro;
    struct {
      Sexp *a;
      Sexp *d;
    } pair;
    Primitive primitive;
    char *string;
    char *symbol;
  } value;
};

#define closure_args(x) ((x)->value.closure.args)
#define closure_body(x) ((x)->value.closure.body)
#define closure_env(x) ((x)->value.closure.env)
#define error(x) ((x)->value.error)
#define flonum(x) ((x)->value.flonum)
#define integer(x) ((x)->value.integer)
#define macro_args(x) ((x)->value.macro.args)
#define macro_body(x) ((x)->value.macro.body)
#define pair(x) ((x)->value.pair)
#define primitive(x) ((x)->value.primitive)
#define string(x) ((x)->value.string)
#define symbol(x) ((x)->value.symbol)

#define isclosure(x) ((x)->type == SEXP_CLOSURE)
#define iserror(x) ((x)->type == SEXP_ERROR)
#define isflonum(x) ((x)->type == SEXP_FLONUM)
#define isinteger(x) ((x)->type == SEXP_INTEGER)
#define ismacro(x) ((x)->type == SEXP_MACRO)
#define isnil(x) ((x)->type == SEXP_NIL)
#define ispair(x) ((x)->type == SEXP_PAIR)
#define isprimitive(x) ((x)->type == SEXP_PRIMITIVE)
#define isstring(x) ((x)->type == SEXP_STRING)
#define issymbol(x) ((x)->type == SEXP_SYMBOL)
#define istrue(x) ((x)->type == SEXP_TRUE)

#define car(x) ((x)->value.pair.a)
#define cdr(x) ((x)->value.pair.d)

struct gc_alloc {
  Sexp sexp;
  unsigned int mark : 1;
  struct gc_alloc *next;
};

struct gc_root {
  struct gc_alloc *alloc;
  struct gc_root *next;
};

/* -- GLOBALS ---------------------------------------------------------------- */

#define GC_PER_ALLOCS 1

struct gc_alloc *gc_allocs = NULL;
struct gc_root *gc_roots = NULL;
unsigned int gc_count = GC_PER_ALLOCS;
int gc_running = 0;

Sexp *globals;
Sexp *interns;
Sexp *nil;
Sexp *t;

Sexp *s_define;
Sexp *s_defmacro;
Sexp *s_if;
Sexp *s_lambda;
Sexp *s_nil;
Sexp *s_quote;
Sexp *s_rest;

/* -- GC --------------------------------------------------------------------- */

Sexp *cons(Sexp *, Sexp *);

struct gc_alloc *
sexp2alloc(Sexp *sexp)
{
  return (struct gc_alloc *) ((char *) sexp - offsetof(struct gc_alloc, sexp));
}

void
gc_protect(Sexp *sexp)
{
  struct gc_root *root = malloc(sizeof(struct gc_root));
  root->alloc = sexp2alloc(sexp);
  root->next = gc_roots;
  gc_roots = root;
}

void
gc_unprotect(Sexp *sexp)
{
  struct gc_alloc *alloc = sexp2alloc(sexp);
  struct gc_root *root, *prev = NULL;
  for (root = gc_roots; root != NULL; root = root->next) {
    if (root->alloc == alloc) {
      if (prev) { prev->next = root->next; } else { gc_roots = root->next; }
      free(root);
      break;
    }
    prev = root;
  }
}

void
gc_mark_sexp(Sexp *sexp)
{
  if (sexp2alloc(sexp)->mark) { return; }
  sexp2alloc(sexp)->mark = 1;
  if (ispair(sexp)) {
    gc_mark_sexp(car(sexp));
    gc_mark_sexp(cdr(sexp));
  }
}

void
gc_mark()
{
  struct gc_root *root;
  for (root = gc_roots; root != NULL; root = root->next) {
    gc_mark_sexp(&root->alloc->sexp);
  }
}

void
gc_sweep()
{
  struct gc_alloc *alloc = gc_allocs, *prev = NULL;
  while (alloc) {
    if (!alloc->mark) {
      if (prev) { prev->next = alloc->next; } else { gc_allocs = alloc->next; }
      if (iserror(&alloc->sexp)) { free(error(&alloc->sexp)); }
      else if (isstring(&alloc->sexp)) { free(string(&alloc->sexp)); }
      free(alloc);
      if (prev) { alloc = prev->next; } else { alloc = gc_allocs; }
    } else {
      alloc->mark = 0;
      prev = alloc;
      alloc = alloc->next;
    }
  }
}

void gc_run() { gc_mark(); gc_sweep(); }

void gc_start() { gc_running = 1; gc_run(); }

Sexp *
gc_safe_cons(Sexp *a, Sexp *d)
{
  Sexp *c = cons(a, d);
  gc_protect(c);
  return c;
}

Sexp *
gc_safe_insert(Sexp *list, Sexp *item)
{
  Sexp *oldlist = list;
  list = cons(item, oldlist);
  gc_protect(list);
  gc_unprotect(oldlist);
  return list;
}

Sexp *
new_sexp(enum sexp_type type)
{
  struct gc_alloc *alloc;
  if (gc_running && !gc_count--) {
    gc_count = GC_PER_ALLOCS;
    gc_run();
  }
  alloc = malloc(sizeof(struct gc_alloc));
  alloc->mark = 0;
  alloc->next = gc_allocs;
  gc_allocs = alloc;
  alloc->sexp.type = type;
  return &alloc->sexp;
}

/* -- CONSTRUCTORS ----------------------------------------------------------- */

Sexp *
cons(Sexp *a, Sexp *d)
{
  Sexp *sexp = new_sexp(SEXP_PAIR);
  car(sexp) = a;
  cdr(sexp) = d;
  return sexp;
}

Sexp *
intern(char *str)
{
  char *sym = malloc(strlen(str) + 1);
  int i = 0;
  Sexp *j, *sexp, *new_interns;
  for (; *str != '\0'; str++) { sym[i++] = toupper(*str); }
  sym[i] = '\0';
  for (j = interns; !isnil(j); j = cdr(j)) {
    if (strcmp(symbol(car(j)), sym) == 0) {
      free(sym);
      return car(j);
    }
  }
  sexp = new_sexp(SEXP_SYMBOL);
  symbol(sexp) = sym;
  gc_protect(sexp);
  new_interns = cons(sexp, interns);
  gc_unprotect(interns);
  interns = new_interns;
  gc_protect(interns);
  gc_unprotect(sexp);
  return sexp;
}

Sexp *
make_closure(Sexp *args, Sexp *body, Sexp *env)
{
  Sexp *sexp = new_sexp(SEXP_CLOSURE);
  closure_args(sexp) = args;
  closure_body(sexp) = body;
  closure_env(sexp) = env;
  return sexp;
}

Sexp *
make_error(char *msg)
{
  char *dup = malloc(strlen(msg) + 1);
  Sexp *sexp;
  sexp = new_sexp(SEXP_ERROR);
  error(sexp) = strcpy(dup, msg);
  return sexp;
}

Sexp *
make_flonum(float flonum)
{
  Sexp *sexp = new_sexp(SEXP_FLONUM);
  flonum(sexp) = flonum;
  return sexp;
}

Sexp *
make_integer(int integer)
{
  Sexp *sexp = new_sexp(SEXP_INTEGER);
  integer(sexp) = integer;
  return sexp;
}

Sexp *
make_macro(Sexp *args, Sexp *body)
{
  Sexp *sexp = new_sexp(SEXP_MACRO);
  macro_args(sexp) = args;
  macro_body(sexp) = body;
  return sexp;
}

Sexp *make_nil() { return new_sexp(SEXP_NIL); }

Sexp *
make_primitive(Primitive primitive)
{
  Sexp *sexp = new_sexp(SEXP_PRIMITIVE);
  primitive(sexp) = primitive;
  return sexp;
}

Sexp *
make_string(char *str)
{
  Sexp *sexp = new_sexp(SEXP_STRING);
  string(sexp) = str;
  return sexp;
}

Sexp *make_true() { return new_sexp(SEXP_TRUE); }

void
print_sexp(Sexp *sexp)
{
  switch (sexp->type) {
  case SEXP_PAIR:
    printf("(");
    for (; ispair(sexp); sexp = cdr(sexp)) {
      print_sexp(car(sexp));
      if (!isnil(cdr(sexp))) printf(" ");
    }
    if (!isnil(sexp)) {
      printf(". ");
      print_sexp(sexp);
    }
    printf(")");
    break;
  case SEXP_CLOSURE: printf("#<CLOSURE>"); break;
  case SEXP_ERROR: printf("%s", error(sexp)); break;
  case SEXP_FLONUM: printf("%g", flonum(sexp)); break;
  case SEXP_INTEGER: printf("%d", integer(sexp)); break;
  case SEXP_MACRO: printf("#<MACRO>"); break;
  case SEXP_NIL: printf("NIL"); break;
  case SEXP_PRIMITIVE: printf("#<PRIMITIVE>"); break;
  case SEXP_STRING: printf("\"%s\"", string(sexp)); break;
  case SEXP_SYMBOL: printf("%s", symbol(sexp)); break;
  case SEXP_TRUE: printf("T"); break;
  }
}

/* -- READERS ---------------------------------------------------------------- */

Sexp *read_sexp(FILE *);

int isdquote(int c) { return c == '"'; }
int isparen(int c) { return c == '(' || c ==')'; }
int isquote(int c) { return c == '\''; }
int issemi(int c) { return c == ';'; }
int issign(int c) { return c == '+' || c == '-'; }

int
ischar(int c)
{
  return !isdigit(c) && !isdquote(c) && !isparen(c) && !isquote(c) &&
    !issemi(c) && !issign(c) && !isspace(c);
}

void
eatblank(FILE *stream)
{
  int c = getc(stream);
  while (isblank(c)) { c = getc(stream); }
  ungetc(c, stream);
}

int
peekc(FILE *stream)
{
  int c;
  eatblank(stream);
  c = getc(stream); ungetc(c, stream);
  return c;
}

Sexp *
read_char(FILE *stream)
{
  char buf[1024];
  int c, i;
  for (c = getc(stream), i = 0;
       ischar(c) || isdigit(c) || issign(c);
       c = getc(stream), i++) { buf[i] = c; }
  buf[i] = '\0';
  ungetc(c, stream);
  return intern(buf);
}

Sexp *
read_digit(FILE *stream)
{
  char buf[1024];
  int c, i;
  for (c = getc(stream), i = 0;
       isdigit(c) || issign(c) || c == '.';
       c = getc(stream), i++) { buf[i] = c; }
  buf[i] = '\0';
  ungetc(c, stream);
  return strchr(buf, '.') ?
    make_flonum(strtof(buf, NULL)) :
    make_integer(atoi(buf));
}

Sexp *
read_dquote(FILE *stream)
{
  char buf[1024], *dup;
  int c, i;
  (void) getc(stream);
  for (c = getc(stream), i = 0; c != '"'; c = getc(stream), i++) { buf[i] = c; }
  buf[i] = '\0';
  dup = malloc(strlen(buf) + 1);
  strcpy(dup, buf);
  return make_string(dup);
}

Sexp *
read_paren(FILE *stream)
{
  Sexp *first, *last;
  Sexp *a, *c, *d;
  (void) getc(stream);
  first = last = nil;
  while (peekc(stream) != ')') {
    a = read_sexp(stream);
    gc_protect(a);
    if (peekc(stream) == '.') {
      (void) getc(stream);
      d = read_sexp(stream);
      gc_protect(d);
      c = cons(a, d);
      gc_protect(c);
      gc_unprotect(a);
      gc_unprotect(d);
    } else {
      c = cons(a, nil);
      gc_protect(c);
      gc_unprotect(a);
    }
    if (isnil(first)) { first = last = c; gc_protect(first); }
    else { last = cdr(last) = c; }
    gc_unprotect(c);
  }
  (void) getc(stream);
  return first;
}

Sexp *
read_quote(FILE *stream)
{
  Sexp *arg, *ret;
  (void) getc(stream);
  arg = read_sexp(stream);
  if (iserror(arg)) { return arg; }
  gc_protect(arg);
  ret = gc_safe_cons(arg, nil);
  gc_unprotect(arg);
  ret = gc_safe_insert(ret, s_quote);
  gc_unprotect(ret);
  return ret;
}

Sexp *
read_sexp(FILE *stream)
{
  int c, c2;
  eatblank(stream);
  c = peekc(stream);
  if (isdigit(c)) { return read_digit(stream); }
  else if (isdquote(c)) { return read_dquote(stream); }
  else if (isparen(c)) { return read_paren(stream); }
  else if (isquote(c)) { return read_quote(stream); }
  else if (ischar(c)) { return read_char(stream); }
  else if (issemi(c)) {
    while (c != '\n') { c = getc(stream); }
    return NULL;
  } else if (issign(c)) {
    c = getc(stream); c2 = getc(stream); ungetc(c2, stream); ungetc(c, stream);
    return isdigit(c2) ? read_digit(stream) : read_char(stream);
  } else if (isspace(c)) {
    while (isspace(c)) { c = getc(stream); }
    ungetc(c, stream);
    return NULL;
  } else {
    (void) getc(stream);
    return make_error("syntax error");
  }
}

/* -- ENV -------------------------------------------------------------------- */

Sexp *make_env(Sexp *parent) { return cons(parent, nil); }

Sexp *
env_set(Sexp *env, Sexp *symbol, Sexp *value)
{
  Sexp *x = cdr(env);
  while (!isnil(x)) {
    if (car(car(x)) == symbol) {
      cdr(car(x)) = value;
      return symbol;
    }
    x = cdr(x);
  }
  x = cons(symbol, value);
  gc_protect(x);
  cdr(env) = cons(x, cdr(env));
  gc_unprotect(x);
  return symbol;
}

Sexp *
env_get(Sexp *env, Sexp *sym)
{
  Sexp *x = cdr(env);
  while (!isnil(x)) {
    if (car(car(x)) == sym) {
      return cdr(car(x));
    }
    x = cdr(x);
  }
  if (!isnil(car(env))) {
    return env_get(car(env), sym);
  }
  return make_error("symbol is unbound");
}

/* -- LIST HELPERS ----------------------------------------------------------- */

Sexp *
list_get(Sexp *list, unsigned int i)
{
  while (i--) { list = cdr(list); }
  return car(list);
}

unsigned int
list_size(Sexp *list)
{
  unsigned int size = 0;
  for (; !isnil(list); list = cdr(list)) { size++; }
  return size;
}

/* -- PRIMITIVES ------------------------------------------------------------- */

#define assert_argc(x, y)                                               \
  if (list_size((x)) != y) { return make_error("wrong number of arguments"); }

#define assert_argt(x, y)                                               \
  if ((x)->type != (y)) { return make_error("wrong argument type"); }

#define arithmetic(NAME, OP)                                    \
  Sexp *                                                        \
  NAME(Sexp *args, __attribute__((unused)) Sexp *env)           \
  {                                                             \
    Sexp *x, *y;                                                \
    assert_argc(args, 2);                                       \
    x = car(args); y = car(cdr(args));                          \
    if ((!isinteger(x) && !(isflonum(x))) ||                    \
        (!isinteger(y) && !isflonum(y))) {                      \
      return make_error("wrong argument type");                 \
    }                                                           \
    if (isinteger(x) && isinteger(y)) {                         \
      return make_integer(integer(x) OP integer(y));            \
    } else if (isinteger(x) && isflonum(y)) {                   \
      return make_flonum(integer(x) OP flonum(y));              \
    } else if (isflonum(x) && isflonum(y)) {                    \
      return make_flonum(flonum(x) OP flonum(y));               \
    } else { /* isflonum(x) && isinteger(y) */                  \
      return make_flonum(flonum(x) OP integer(y));              \
    }                                                           \
  }

arithmetic(primitive_add, +)
arithmetic(primitive_divide, /)
arithmetic(primitive_multiply, *)
arithmetic(primitive_subtract, -)

#define comparison(NAME, OP)                                    \
  Sexp *                                                        \
  NAME(Sexp *args, __attribute__((unused)) Sexp *env)           \
  {                                                             \
    Sexp *x, *y;                                                \
    assert_argc(args, 2);                                       \
    x = car(args); y = car(cdr(args));                          \
    if ((!isinteger(x) && !(isflonum(x))) ||                    \
        (!isinteger(y) && !isflonum(y))) {                      \
      return make_error("wrong argument type");                 \
    }                                                           \
    if (isinteger(x) && isinteger(y)) {                         \
      return integer(x) OP integer(y) ? t : nil;                \
    } else if (isinteger(x) && isflonum(y)) {                   \
      return integer(x) OP flonum(y) ? t : nil;                 \
    } else if (isflonum(x) && isflonum(y)) {                    \
      return flonum(x) OP flonum(y) ? t : nil;                  \
    } else { /* isflonum(x) && isinteger(y) */                  \
      return flonum(x) OP integer(y) ? t : nil;                 \
    }                                                           \
  }

comparison(primitive_numeq, ==)
comparison(primitive_ge, >=)
comparison(primitive_gt, >)
comparison(primitive_le, <=)
comparison(primitive_lt, <)
comparison(primitive_ne, !=)

Sexp *
primitive_atom(Sexp *args, __attribute__((unused)) Sexp *env)
{
  assert_argc(args, 1);
  return !ispair(car(args)) ? t : nil;
}

Sexp *
primitive_car(Sexp *args, __attribute__((unused)) Sexp *env)
{
  assert_argc(args, 1);
  if (isnil(car(args))) { return nil; }
  assert_argt(car(args), SEXP_PAIR);
  return car(car(args));
}

Sexp *
primitive_cdr(Sexp *args, __attribute__((unused)) Sexp *env)
{
  assert_argc(args, 1);
  if (isnil(car(args))) { return nil; }
  assert_argt(car(args), SEXP_PAIR);
  return cdr(car(args));
}

Sexp *
primitive_cons(Sexp *args, __attribute__((unused)) Sexp *env)
{
  assert_argc(args, 2);
  return cons(car(args), car(cdr(args)));
}

Sexp *
primitive_eq(Sexp *args, __attribute__((unused)) Sexp *env)
{
  assert_argc(args, 2);
  return car(args) == car(cdr(args)) ? t : nil;
}

Sexp *
primitive_print(Sexp *args, __attribute__((unused)) Sexp *env)
{
  assert_argc(args, 1);
  print_sexp(car(args));
  printf("\n");
  return nil;
}

/* -- EVAL ------------------------------------------------------------------- */

#define F_PARENT car(frame)
#define F_ENV car(cdr(frame))
#define F_SEXP car(cdr(cdr(frame)))
#define F_ARGS car(cdr(cdr(cdr(frame))))
#define F_VAL car(cdr(cdr(cdr(cdr(frame)))))
#define F_OP car(cdr(cdr(cdr(cdr(cdr(frame))))))

Sexp *
push_frame(Sexp *parent, Sexp *env, Sexp *s)
{
  Sexp *frame = gc_safe_cons(nil, nil);
  frame = gc_safe_insert(frame, nil);
  frame = gc_safe_insert(frame, nil);
  frame = gc_safe_insert(frame, s);
  frame = gc_safe_insert(frame, env);
  frame = gc_safe_insert(frame, parent);
  if (!isnil(parent)) { gc_unprotect(parent); }
  return frame;
}

#define f_assert_argc(list, count)                   \
  if (list_size(list) != count) {                    \
    F_VAL = make_error("wrong number of arguments"); \
    goto pop;                                        \
  }

#define f_assert_argtype(arg, argtype)          \
  if (arg->type != argtype) {                   \
    F_VAL = make_error("wrong argument type");  \
    goto pop;                                   \
  }

Sexp *
eval_sexp(Sexp *sexp, Sexp *env)
{
  Sexp *x, *y;
  Sexp *val;
  Sexp *frame = push_frame(nil, env, sexp);
 loop:
  if (ispair(F_SEXP) && car(F_SEXP) == s_define) {
    if (list_size(F_SEXP) == 4) {
      f_assert_argtype(car(cdr(F_SEXP)), SEXP_SYMBOL);
      if (!ispair(list_get(F_SEXP, 2)) && !isnil(list_get(F_SEXP, 2))) {
        F_VAL = make_error("wrong argument type");
        goto pop;
      }
      x = make_closure(car(cdr(cdr(F_SEXP))), car(cdr(cdr(cdr(F_SEXP)))), F_ENV);
      gc_protect(x);
      env_set(F_ENV, car(cdr(F_SEXP)), x);
      gc_unprotect(x);
      F_VAL = car(cdr(F_SEXP));
    } else if (list_size(F_SEXP) == 3) {
      f_assert_argtype(car(cdr(F_SEXP)), SEXP_SYMBOL);
      if (isnil(F_ARGS)) {
        sexp = list_get(F_SEXP, 2);
        frame = push_frame(frame, F_ENV, sexp);
        goto loop;
      }
      env_set(F_ENV, car(F_ARGS), car(cdr(F_ARGS)));
      F_VAL = car(F_ARGS);
    } else {
      F_VAL = make_error("wrong number of arguments");
      goto pop;
    }
  } else if (ispair(F_SEXP) && car(F_SEXP) == s_quote) {
    f_assert_argc(F_SEXP, 2);
    F_VAL = car(cdr(F_SEXP));
  } else if (ispair(F_SEXP) && car(F_SEXP) == s_lambda) {
    f_assert_argc(F_SEXP, 3);
    if (!ispair(list_get(F_SEXP, 1)) && !isnil(list_get(F_SEXP, 1))) {
      F_VAL = make_error("wrong argument type");
      goto pop;
    }
    F_VAL = make_closure(car(cdr(F_SEXP)), car(cdr(cdr(F_SEXP))), F_ENV);
  } else if (ispair(F_SEXP) && car(F_SEXP) == s_if) {
    f_assert_argc(F_SEXP, 4);
    if (isnil(F_ARGS)) {
      sexp = list_get(F_SEXP, 1);
      frame = push_frame(frame, F_ENV, sexp);
      goto loop;
    } else if (list_size(F_ARGS) == 1) {
      if (!isnil(list_get(F_ARGS, 0))) {
        sexp = list_get(F_SEXP, 2);
      } else {
        sexp = list_get(F_SEXP, 3);
      }
      frame = push_frame(frame, F_ENV, sexp);
      goto loop;
    }
    if (!isnil(list_get(F_ARGS, 0))) {
      F_VAL = list_get(F_ARGS, 1);
    } else {
      F_VAL = list_get(F_ARGS, 2);
    }
  } else if (ispair(F_SEXP) && car(F_SEXP) == s_defmacro) {
    f_assert_argc(F_SEXP, 4);
    f_assert_argtype(car(cdr(F_SEXP)), SEXP_SYMBOL);
    if (!ispair(list_get(F_SEXP, 2)) && !isnil(list_get(F_SEXP, 2))) {
      F_VAL = make_error("wrong argument type");
      goto pop;
    }
    x = make_macro(list_get(F_SEXP, 2), list_get(F_SEXP, 3));
    gc_protect(x);
    env_set(F_ENV, car(cdr(F_SEXP)), x);
    gc_unprotect(x);
    F_VAL = car(cdr(F_SEXP));
  } else if (ispair(F_SEXP)) {
    if (isnil(F_OP)) {
      sexp = car(F_SEXP);
      frame = push_frame(frame, F_ENV, sexp);
      goto loop;
    }
    if (ismacro(F_OP)) {
      f_assert_argc(macro_args(F_OP), list_size(F_SEXP) - 1);
    } else if (isclosure(F_OP)) {
      f_assert_argc(closure_args(F_OP), list_size(F_SEXP) - 1);
    } else if (!isprimitive(F_OP)) {
      F_VAL = make_error("wrong operator type");
      goto pop;
    }
    if (list_size(F_ARGS) != list_size(F_SEXP) - 1) {
      sexp = list_get(F_SEXP, list_size(F_ARGS) + 1);
      frame = push_frame(frame, F_ENV, sexp);
      goto loop;
    }
    if (ismacro(F_OP)) {
      F_ENV = make_env(F_ENV);
      for (x = macro_args(F_OP), y = F_ARGS;
           !isnil(x);
           x = cdr(x), y = cdr(y)) {
        env_set(F_ENV, car(x), car(y));
      }
      sexp = macro_body(F_OP);
      frame = push_frame(F_PARENT, F_ENV, sexp);
      goto loop;
    } else if (isclosure(F_OP)) {
      F_ENV = make_env(closure_env(F_OP));
      for (x = closure_args(F_OP), y = F_ARGS;
           !isnil(x);
           x = cdr(x), y = cdr(y)) {
        if (car(x) == s_rest) {
          env_set(F_ENV, car(cdr(x)), y);
          break;
        } else {
          env_set(F_ENV, car(x), car(y));
        }
      }
      sexp = closure_body(F_OP);
      frame = push_frame(F_PARENT, F_ENV, sexp);
      goto loop;
    } else if (isprimitive(F_OP)) {
      F_VAL = primitive(F_OP)(F_ARGS, F_ENV);
    }
  } else if (issymbol(F_SEXP)) {
    F_VAL = env_get(F_ENV, F_SEXP);
  } else {
    F_VAL = F_SEXP;
  }
 pop:
  if (!isnil(F_PARENT)) {
    if (iserror(F_VAL)) { goto ret; }
    val = F_VAL;
    gc_protect(val);
    gc_protect(F_PARENT);
    gc_unprotect(frame);
    frame = F_PARENT;
    if (car(F_SEXP) == s_define) {
      F_ARGS = cons(car(cdr(F_SEXP)), nil);
      cdr(F_ARGS) = cons(val, nil);
    } else if (car(F_SEXP) == s_if) {
      if (isnil(F_ARGS)) {
        F_ARGS = cons(val, nil);
      } else {
        if (!isnil(car(F_ARGS))) {
          x = car(F_ARGS);
          gc_protect(x);
          F_ARGS = cons(list_get(F_SEXP, 3), nil);
          F_ARGS = cons(val, F_ARGS);
          F_ARGS = cons(x, F_ARGS);
          gc_unprotect(x);
        } else {
          x = car(F_ARGS);
          gc_protect(x);
          F_ARGS = cons(val, nil);
          F_ARGS = cons(list_get(F_SEXP, 2), F_ARGS);
          F_ARGS = cons(x, F_ARGS);
          gc_unprotect(x);
        }
      }
    } else {
      if (isnil(F_OP)) {
        F_OP = val;
      } else {
        if (isnil(F_ARGS)) {
          F_ARGS = cons(val, nil);
        } else {
          for (x = F_ARGS; !isnil(cdr(x)); x = cdr(x));
          cdr(x) = cons(val, nil);
        }
      }
    }
    gc_unprotect(val);
    goto loop;
  }
 ret:
  gc_unprotect(frame);
  return F_VAL;
}

/* -- MAIN ------------------------------------------------------------------- */

void
repl()
{
  char *prompt = "* ";
  Sexp *input;
  while (!feof(stdin)) {
    printf(prompt);
  repeat:
    input = read_sexp(stdin);
    if (!input) { goto repeat; }
    gc_protect(input);
    print_sexp(eval_sexp(input, globals));
    printf("\n");
    gc_unprotect(input);
  }
}

int
main()
{
  nil = make_nil(); gc_protect(nil);
  t = make_true(); gc_protect(t);
  interns = nil;
  
  s_define = intern("DEFINE");
  s_defmacro = intern("DEFMACRO");
  s_if = intern("IF");
  s_lambda = intern("LAMBDA");
  s_nil = intern("NIL");
  s_quote = intern("QUOTE");
  s_rest = intern("&REST");

  globals = make_env(nil); gc_protect(globals);
  env_set(globals, intern("nil"), nil);
  env_set(globals, intern("t"), t);
  env_set(globals, intern("*"), make_primitive(primitive_multiply));
  env_set(globals, intern("+"), make_primitive(primitive_add));
  env_set(globals, intern("-"), make_primitive(primitive_subtract));
  env_set(globals, intern("/"), make_primitive(primitive_divide));
  env_set(globals, intern("/="), make_primitive(primitive_ne));
  env_set(globals, intern("<"), make_primitive(primitive_lt));
  env_set(globals, intern("<="), make_primitive(primitive_le));
  env_set(globals, intern("="), make_primitive(primitive_numeq));
  env_set(globals, intern(">"), make_primitive(primitive_gt));
  env_set(globals, intern(">="), make_primitive(primitive_ge));
  env_set(globals, intern("atom"), make_primitive(primitive_atom));
  env_set(globals, intern("car"), make_primitive(primitive_car));
  env_set(globals, intern("cdr"), make_primitive(primitive_cdr));
  env_set(globals, intern("cons"), make_primitive(primitive_cons));
  env_set(globals, intern("eq"), make_primitive(primitive_eq));
  env_set(globals, intern("print"), make_primitive(primitive_print));

  gc_start();
  repl();
  return 0;
}
