#include <stdio.h>
#include <stdlib.h>

#include <readline/readline.h>
#include <readline/history.h>

#include "includes/mpc.h"

// I should put this somewhere else
void print_err(char* err) {
    printf("\e[31m\e[1mError:\e[0m");
    printf(" %s", err);
}

mpc_parser_t* Number;
mpc_parser_t* Symbol;
mpc_parser_t* String;
mpc_parser_t* Comment;
mpc_parser_t* Pringle;
mpc_parser_t* List;
mpc_parser_t* Expr;
mpc_parser_t* Crisp;

enum {
    VAL_NUM, // Number
    VAL_ERR, // Error
    VAL_SYM, // Symbol
    VAL_STR, // String
    VAL_FUN, // Function
    VAL_PRI, // Pringle
    VAL_LST, // List
};

/**
 * Get the human-readable string from the value type
 */
char* type_name(int t) {
    switch (t) {
        case VAL_NUM: return "Number";
        case VAL_ERR: return "Error";
        case VAL_SYM: return "Symbol";
        case VAL_STR: return "String";
        case VAL_FUN: return "Function";
        case VAL_PRI: return "Pringle";
        case VAL_LST: return "List";
        default:      return "Unknown";
    }
}

struct val;
struct env;
typedef struct val val;
typedef struct env env;

typedef val*(*builtin)(env*, val*);

// Value type
typedef struct val {
    int type;          // Type (enum)
    double num;        // Number value
    char* err;         // Error message
    char* sym;         // Symbol
    char* str;         // String
    builtin builtin;   // Function
    env* env;          // Environment
    val* arguments;    // Function arguments
    val* body;         // Function body
    int count;         // Number of children
    struct val** cell; // Children
} val;

// Environment type
struct env {
    env* parent;
    int count;
    char** symbols;
    val** values;
};

/*
 * Values
 */

/**
 * Copy a value
 */
env* env_copy(env* e);
val* val_copy(val* v) {
    val* x = malloc(sizeof(val));
    x->type = v->type;
    switch (v->type) {
        case VAL_NUM: x->num = v->num; break;
        case VAL_ERR:
            x->err = malloc(strlen(v->err) + 1);
            strcpy(x->err, v->err);
            break;
        case VAL_SYM:
            x->sym = malloc(strlen(v->sym) + 1);
            strcpy(x->sym, v->sym);
            break;
        case VAL_STR:
            x->str = malloc(strlen(v->str) + 1);
            strcpy(x->str, v->str);
            break;
        case VAL_PRI:
        case VAL_LST:
            x->count = v->count;
            x->cell = malloc(sizeof(val*) * x->count);
            for (int i = 0; i < x->count; i++) {
                x->cell[i] = val_copy(v->cell[i]);
            }
            break;
        case VAL_FUN:
            if (v->builtin) {
                x->builtin = v->builtin;
            } else {
                x->builtin = NULL;
                x->env = env_copy(v->env);
                x->arguments = val_copy(v->arguments);
                x->body = val_copy(v->body);
            }
            break;
    }
    return x;
}

/**
 * Recursively destroy values
 */
void env_del(env* e);
void val_del(val* v) {
    switch (v->type) {
        case VAL_ERR: free(v->err); break;
        case VAL_SYM: free(v->sym); break;
        case VAL_STR: free(v->str); break;
        case VAL_PRI:
        case VAL_LST:
            for (int i = 0; i < v->count; i++) {
                val_del(v->cell[i]);
            }
            free(v->cell);
            break;
        case VAL_FUN:
            if (!v->builtin) {
                env_del(v->env);
                val_del(v->arguments);
                val_del(v->body);
            }
            break;
    }
    free(v);
}

/**
 * Append val struct x onto val struct v
 */
val* val_add(val* v, val* x) {
    v->count++;
    v->cell = realloc(v->cell, sizeof(val*) * v->count);
    v->cell[v->count - 1] = x;
    return v;
}

/**
 * Remove the given child and return it
 */
val* val_pop(val* v, int i) {
    val* x = v->cell[i];
    memmove(&v->cell[i], &v->cell[i + 1], sizeof(val*) * (v->count - i - 1));
    v->count--;
    v->cell = realloc(v->cell, sizeof(val*) * v->count);
    return x;
}

/**
 * Unsure
 */
val* val_take(val* v, int i) {
    val* x = val_pop(v, i);
    val_del(v);
    return x;
}

/**
 * Join two or more values
 */
val* val_join(val* x, val* y) {
    while (y->count) {
        x = val_add(x, val_pop(y, 0));
    }
    val_del(y);
    return x;
}

/**
 * Construct a new number
 */
val* val_num(double x) {
    val* v = malloc(sizeof(val));
    v->type = VAL_NUM;
    v->num = x;
    return v;
}

/**
 * Construct a new error
 */
val* val_err(char* fmt, ...) {
    val* v = malloc(sizeof(val));
    v->type = VAL_ERR;
    va_list va;
    va_start(va, fmt);
    v->err = malloc(512);
    vsnprintf(v->err, 511, fmt, va);
    v->err = realloc(v->err, strlen(v->err) + 1);
    va_end(va);
    return v;
}

/**
 * Construct a new symbol
 */
val* val_sym(char* s) {
    val* v = malloc(sizeof(val));
    v->type = VAL_SYM;
    v->sym = malloc(strlen(s) + 1);
    strcpy(v->sym, s);
    return v;
}

/**
 * Construct a new string
 */
val* val_str(char* s) {
    val* v = malloc(sizeof(val));
    v->type = VAL_STR;
    v->str = malloc(strlen(s) + 1);
    strcpy(v->str, s);
    return v;
}

/**
 * Construct a new function pointer
 */
val* val_fun(builtin func) {
    val* v = malloc(sizeof(val));
    v->type = VAL_FUN;
    v->builtin = func;
    return v;
}

/**
 * Construct a new pringle
 */
val* val_pringle(void) {
    val* v = malloc(sizeof(val));
    v->type = VAL_PRI;
    v->count = 0;
    v->cell = NULL;
    return v;
}

/**
 * Construct a new list
 */
val* val_list(void) {
    val* v = malloc(sizeof(val));
    v->type = VAL_LST;
    v->count = 0;
    v->cell = NULL;
    return v;
}

/**
 * Construct a new Function
 */
env* env_new(void);
val* val_lambda(val* arguments, val* body) {
    val* v = malloc(sizeof(val));
    v->type = VAL_FUN;
    v->builtin = NULL;
    v->env = env_new();
    v->arguments = arguments;
    v->body = body;
    return v;
}

/**
 * Print an Expression
 */
void val_print(val* v);
void val_expr_print(val* v, char open, char close) {
    putchar(open);
    for (int i = 0; i < v->count; i++) {
        val_print(v->cell[i]);
        if (i != (v->count - 1)) {
            putchar(' ');
        }
    }
    putchar(close);
}

/**
 * Print a string
 */
void val_print_str(val* v) {
    char* escaped = malloc(strlen(v->str) + 1);
    strcpy(escaped, v->str);
    escaped = mpcf_escape(escaped);
    printf("\"%s\"", escaped);
    free(escaped);
}

/**
 * Print the value's structure
 */
void val_print(val* v) {
    switch (v->type) {
        case VAL_NUM: printf("%g", v->num);       break;
        case VAL_ERR: print_err(v->err);           break;
        case VAL_SYM: printf(v->sym);              break;
        case VAL_STR: val_print_str(v);            break;
        case VAL_PRI: val_expr_print(v, '(', ')'); break;
        case VAL_LST: val_expr_print(v, '{', '}'); break;
        case VAL_FUN:
            if (v->builtin) {
                printf("<builtin>");
            } else {
                printf("(\\ ");
                val_print(v->arguments);
                putchar(' ');
                val_print(v->body);
                putchar(')');
            }
            break;
    }
}

/**
 * Print the value's structure with a newline
 */
void val_println(val* v) {
    val_print(v);
    putchar('\n');
}

/**
 * Equality comparison
 */
int val_eq(val* x, val* y) {
    if (x->type != y->type) { return 0; }
    switch(x->type) {
        case VAL_NUM: return (x->num == y->num);
        case VAL_ERR: return (strcmp(x->err, y->err) == 0);
        case VAL_SYM: return (strcmp(x->sym, y->sym) == 0);
        case VAL_STR: return (strcmp(x->str, y->str) == 0);
        case VAL_FUN:
            if (x->builtin || y->builtin) {
                return x->builtin == y->builtin;
            }
            return val_eq(x->arguments, y->arguments) && val_eq(x->body, y->body);
        case VAL_LST:
        case VAL_PRI:
            if (x->count != y->count) { return 0; }
            for (int i = 0; i < x->count; i++) {
                if (!val_eq(x->cell[i], y->cell[i])) { return 0; }
            }
            return 1;
    }
    return 0;
}

/**
 * Call non-builtin Functions
 */
void env_put(env* e, val* k, val* v);
val* builtin_list(env* e, val* a);
val* builtin_eval(env* e, val* a);
val* val_call(env* e, val* f, val* a) {
    if (f->builtin) { return f->builtin(e, a); }
    int given = a->count;
    int total = f->arguments->count;
    while (a->count) {
        if (f->arguments->count == 0) {
            val_del(a);
            return val_err(
                "Function passed too many arguments\n"
                "Expected %i got %i",
                given, total);
        }
        val* sym = val_pop(f->arguments, 0);
        if (strcmp(sym->sym, "&") == 0) {
            if (f->arguments->count != 1) {
                val_del(a);
                return val_err(
                    "Function format invalid\n"
                    "Symbol '&' not followed by single symbol");
            }
            val* new_symbol = val_pop(f->arguments, 0);
            env_put(f->env, new_symbol, builtin_list(e, a));
            val_del(sym);
            val_del(new_symbol);
            break; // what
        }
        val* val = val_pop(a, 0);
        env_put(f->env, sym, val);
        val_del(sym);
        val_del(val);
    }
    val_del(a);
    if (f->arguments->count > 0 && strcmp(f->arguments->cell[0]->sym, "&") == 0) {
        if (f->arguments->count != 2) {
            return val_err(
                "Function format invalid\n"
                "Symbol '&' not followed by single symbol");
        }
        val_del(val_pop(f->arguments, 0));
        val* symbol = val_pop(f->arguments, 0);
        val* value = val_list();
        env_put(f->env, symbol, value);
        val_del(symbol);
        val_del(value);
    }
    if (f->arguments->count == 0) {
        f->env->parent = e;
        return builtin_eval(f->env, val_add(val_pringle(), val_copy(f->body)));
    }
    return val_copy(f);
}

/**
 * Evaluate a Pringle
 */
val* val_eval(env* e, val* v);
val* val_eval_pringle(env* e, val* v) {
    for (int i = 0; i < v->count; i++) {
        v->cell[i] = val_eval(e, v->cell[i]);
    }
    for (int i = 0; i < v->count; i++) {
        if (v->cell[i]->type == VAL_ERR) {
            return val_take(v, i);
        }
    }
    if (v->count == 0) {
        return v;
    }
    if (v->count == 1) {
        return val_take(v, 0);
    }
    val* f = val_pop(v, 0);
    if (f->type != VAL_FUN) {
        val* err = val_err(
            "Pringle starts with incorrect type\n"
            "Expected Function got %s",
            type_name(f->type));
        val_del(f);
        val_del(v);
        return err;
    }
    val* result = val_call(e, f, v);
    val_del(f);
    return result;
}

/**
 * Evaluate a Function or Pringle
 */
val* env_get(env* e, val* k);
val* val_eval(env* e, val* v) {
    if (v->type == VAL_SYM) {
        val* x = env_get(e, v);
        val_del(v);
        return x;
    }
    if (v->type == VAL_PRI) {
        return val_eval_pringle(e, v);
    }
    return v;
}

/**
 * Read a number value
 */
val* val_read_num(mpc_ast_t* t) {
    errno = 0;
    double x = strtod(t->contents, NULL);
    return errno != ERANGE ? val_num(x) : val_err("Invalid number");
}

/**
 * Read a string value
 */
val* val_read_str(mpc_ast_t* t) {
    t->contents[strlen(t->contents) - 1] = '\0';
    char* unescaped = malloc(strlen(t->contents + 1) + 1);
    strcpy(unescaped, t->contents + 1);
    unescaped = mpcf_unescape(unescaped);
    val* str = val_str(unescaped);
    free(unescaped);
    return str;
}

/**
 * Read main val structure
 */
val* val_read(mpc_ast_t* t) {
    if (strstr(t->tag, "number"))  { return val_read_num(t); }
    if (strstr(t->tag, "symbol"))  { return val_sym(t->contents); }
    if (strstr(t->tag, "string"))  { return val_read_str(t); }
    val* x = NULL;
    if (strcmp(t->tag, ">") == 0)  { x = val_pringle(); }
    if (strstr(t->tag, "pringle")) { x = val_pringle(); }
    if (strstr(t->tag, "list"))    { x = val_list(); }
    for (int i = 0; i < t->children_num; i++) {
        if (strcmp(t->children[i]->contents, "(") == 0 ||
            strcmp(t->children[i]->contents, ")") == 0 ||
            strcmp(t->children[i]->contents, "{") == 0 ||
            strcmp(t->children[i]->contents, "}") == 0 ||
            strstr(t->children[i]->tag, "comment") ||
            strcmp(t->children[i]->tag, "regex") == 0) {
            continue;
        }
        x = val_add(x, val_read(t->children[i]));
    }
    return x;
}

/*
 * Environment
 *
 * The environment stores the variables. Each variable has a symbol and a
 * value. A new environment is created when calling a function in order to
 * create local variables. The environment also inherits variables from its
 * parent environment. When creating functions the parent environment will be
 * the global namespace.
 */

/**
 * Create a new environment
 */
env* env_new(void) {
    env* e = malloc(sizeof(env));
    e->parent = NULL;
    e->count = 0;
    e->symbols = NULL;
    e->values = NULL;
    return e;
}

/**
 * Copy an environment
 */
env* env_copy(env* e) {
    env* n = malloc(sizeof(env));
    n->parent = e->parent;
    n->count = e->count;
    n->symbols = malloc(sizeof(char*) * n->count);
    n->values = malloc(sizeof(val*) * n->count);
    for (int i = 0; i < e->count; i++) {
        n->symbols[i] = malloc(strlen(e->symbols[i]) + 1);
        strcpy(n->symbols[i], e->symbols[i]);
        n->values[i] = val_copy(e->values[i]);
    }
    return n;
}

/**
 * Recursively delete an environment
 */
void env_del(env* e) {
    for (int i = 0; i < e->count; i++) {
        free(e->symbols[i]);
        val_del(e->values[i]);
    }
    free(e->symbols);
    free(e->values);
    free(e);
}

/**
 * Get a value from the environment by symbol
 */
val* env_get(env* e, val* k) {
    for (int i = 0; i < e->count; i++) {
        if (strcmp(e->symbols[i], k->sym) == 0) {
            return val_copy(e->values[i]);
        }
    }
    if (e->parent) {
        return env_get(e->parent, k);
    } else {
        return val_err("Undefined symbol '%s'", k->sym);
    }
}

/**
 * Define a local variable
 */
void env_put(env* e, val* k, val* v) {
    for (int i = 0; i < e->count; i++) {
        if (strcmp(e->symbols[i], k->sym) == 0) {
            val_del(e->values[i]);
            e->values[i] = val_copy(v);
            return;
        }
    }
    e->count++;
    e->values = realloc(e->values, sizeof(val*) * e->count);
    e->symbols = realloc(e->symbols, sizeof(char*) * e->count);
    e->values[e->count - 1] = val_copy(v);
    e->symbols[e->count - 1] = malloc(strlen(k->sym) + 1);
    strcpy(e->symbols[e->count - 1], k->sym);
}

/**
 * Define a global variable
 */
void env_def(env* environment, val* key, val* value) {
    while (environment->parent) { environment = environment->parent; }
    env_put(environment, key, value);
}

/*
 * Builtins
 *
 * Builtins are pre-defined functions that come with the language
 */

#define ASSERT(args, cond, fmt, ...) \
    if (!(cond)) { \
        val* err = val_err(fmt, ##__VA_ARGS__); \
        val_del(args); \
        return err; \
    }

#define ASSERT_TYPE(func, args, index, expect) \
    ASSERT(args, args->cell[index]->type == expect, \
        "Function '%s' passed incorrect type for argument %i\n" \
        "Expected %s got %s", \
        func, index + 1, \
        type_name(expect), type_name(args->cell[index]->type));

#define ASSERT_NUM(func, args, num) \
    ASSERT(args, args->count == num, \
        "Function '%s' passed incorrect number of arguments\n" \
        "Expected %i got %i", \
        func, num, args->count);

#define ASSERT_NOT_EMPTY(func, args, index) \
    ASSERT(args, args->cell[index]->count != 0, \
        "Function '%s' passed {} for argument %i", \
        func, index + 1);

/**
 * Perform operations on numbers
 */
val* builtin_op(env* e, val* a, char* op) {
    for (int i = 0; i < a->count; i++) {
        ASSERT_TYPE(op, a, i, VAL_NUM);
    }
    val* x = val_pop(a, 0);
    if ((strcmp(op, "-") == 0) && a->count == 0) {
        x->num = -x->num;
    }
    while (a->count > 0) {
        val* y = val_pop(a, 0);
        if (strcmp(op, "+") == 0) { x->num += y->num; }
        if (strcmp(op, "-") == 0) { x->num -= y->num; }
        if (strcmp(op, "*") == 0) { x->num *= y->num; }
        if (strcmp(op, "/") == 0) {
            if (y->num == 0) {
                val_del(x);
                val_del(y);
                x = val_err("Division by zero");
                break;
            } else {
                x->num /= y->num;
            }
        }
        val_del(y);
    }
    val_del(a);
    return x;
}

/**
 * Perform variable operations
 */
val* builtin_var(env* e, val* a, char* func) {
    ASSERT_TYPE(func, a, 0, VAL_LST);
    val* syms = a->cell[0];
    for (int i = 0; i < syms->count; i++) {
        ASSERT(a, (syms->cell[i]->type == VAL_SYM),
            "Function '%s' cannot define non-symbol\n"
            "Expected Symbol got %s",
            func, type_name(syms->cell[0]->type));
    }
    ASSERT(a, (syms->count == a->count - 1),
        "Function '%s' passed too many arguments for symbols\n"
        "Expected %i got %i",
        func, syms->count, a->count - 1);
    for (int i = 0; i < syms->count; i++) {
        if (strcmp(func, "def") == 0) {
            env_def(e, syms->cell[i], a->cell[i + 1]);
        } else if (strcmp(func, "=") == 0) {
            env_put(e, syms->cell[i], a->cell[i + 1]);
        }
    }
    val_del(a);
    return val_pringle();
}

/**
 * Perform number comparison operations
 */
val* builtin_ord(env* e, val* a, char* op) {
    ASSERT_NUM(op, a, 2);
    ASSERT_TYPE(op, a, 0, VAL_NUM);
    ASSERT_TYPE(op, a, 1, VAL_NUM);
    int r;
    if (strcmp(op, ">") == 0) {
        r = (a->cell[0]->num > a->cell[1]->num);
    } else if (strcmp(op, "<") == 0) {
        r = (a->cell[0]->num < a->cell[1]->num);
    } else if (strcmp(op, ">=") == 0) {
        r = (a->cell[0]->num >= a->cell[1]->num);
    } else if (strcmp(op, "<=") == 0) {
        r = (a->cell[0]->num <= a->cell[1]->num);
    }
    val_del(a);
    return val_num(r);
}

/**
 * Perform comparison operations with different types
 */
val* builtin_cmp(env* e, val* a, char* op) {
    ASSERT_NUM(op, a, 2);
    int r;
    if (strcmp(op, "==") == 0) {
        r = val_eq(a->cell[0], a->cell[1]);
    } else if (strcmp(op, "!=") == 0) {
        r = !val_eq(a->cell[0], a->cell[1]);
    }
    val_del(a);
    return val_num(r);
}

/**
 * Get the first list item
 */
val* builtin_head(env *e, val* a) {
    ASSERT_NUM("head", a, 1);
    ASSERT_TYPE("head", a, 0, VAL_LST);
    ASSERT_NOT_EMPTY("head", a, 0);
    val* v = val_take(a, 0);
    while (v->count > 1) {
        val_del(val_pop(v, 1));
    }
    return v;
}

/**
 * Get all list items aside from the first
 */
val* builtin_tail(env *e, val* a) {
    ASSERT_NUM("tail", a, 1)
    ASSERT_TYPE("tail", a, 0, VAL_LST);
    ASSERT_NOT_EMPTY("tail", a, 0);
    val* v = val_take(a, 0);
    val_del(val_pop(v, 0));
    return v;
}

/**
 * Convert a Pringle to a List
 */
val* builtin_list(env* e, val* a) {
    a->type = VAL_LST;
    return a;
}

/**
 * Evaluate a List as if it were a Pringle
 */
val* builtin_eval(env* e, val* a) {
    ASSERT_NUM("eval", a, 1);
    ASSERT_TYPE("eval", a, 0, VAL_LST);
    val* x = val_take(a, 0);
    x->type = VAL_PRI;
    return val_eval(e, x);
}

/**
 * Join lists
 */
val* builtin_join(env* e, val* a) {
    for (int i = 0; i < a->count; i++) {
        ASSERT_TYPE("join", a, i, VAL_LST);
    }
    val* x = val_pop(a, 0);
    while (a->count) {
        x = val_join(x, val_pop(a, 0));
    }
    val_del(a);
    return x;
}

/**
 * Add numbers
 */
val* builtin_add(env* e, val* a) {
    return builtin_op(e, a, "+");
}

/**
 * Subtract numbers
 */
val* builtin_sub(env* e, val* a) {
    return builtin_op(e, a, "-");
}

/**
 * Multiply numbers
 */
val* builtin_mul(env* e, val* a) {
    return builtin_op(e, a, "*");
}

/**
 * Divide numbers
 */
val* builtin_div(env* e, val* a) {
    return builtin_op(e, a, "/");
}

/**
 * Define a global variable
 */
val* builtin_def(env* e, val* a) {
    return builtin_var(e, a, "def");
}

/**
 * Define a local variable
 */
val* builtin_put(env* e, val* a) {
    return builtin_var(e, a, "=");
}

/**
 * Greater than comparison
 */
val* builtin_gt(env* e, val* a) {
    return builtin_ord(e, a, ">");
}

/**
 * Less than comparison
 */
val* builtin_lt(env* e, val* a) {
    return builtin_ord(e, a, "<");
}

/**
 * Greater than or equal to comparison
 */
val* builtin_ge(env* e, val* a) {
    return builtin_ord(e, a, ">=");
}

/**
 * Less than or equal to comparison
 */
val* builtin_le(env* e, val* a) {
    return builtin_ord(e, a, "<=");
}

/**
 * Equality comparison
 */
val* builtin_eq(env* e, val* a) {
    return builtin_cmp(e, a, "==");
}

/**
 * Inequality comparison
 */
val* builtin_ne(env* e, val* a) {
    return builtin_cmp(e, a, "!=");
}

/**
 * "if" conditional statement
 */
val* builtin_if(env* e, val* a) {
    ASSERT_NUM("if", a, 3);
    ASSERT_TYPE("if", a, 0, VAL_NUM);
    ASSERT_TYPE("if", a, 1, VAL_LST);
    ASSERT_TYPE("if", a, 2, VAL_LST);
    val* x;
    a->cell[1]->type = VAL_PRI;
    a->cell[2]->type = VAL_PRI;
    if (a->cell[0]->num) {
        x = val_eval(e, val_pop(a, 1));
    } else {
        x = val_eval(e, val_pop(a, 2));
    }
    val_del(a);
    return x;
}

/**
 * Create a function
 */
val* builtin_lambda(env* e, val* a) {
    ASSERT_NUM("\\", a, 2);
    ASSERT_TYPE("\\", a, 0, VAL_LST);
    ASSERT_TYPE("\\", a, 1, VAL_LST);
    for (int i = 0; i < a->cell[0]->count; i++) {
        ASSERT_TYPE("\\", a->cell[0], i, VAL_SYM);
    }
    val* arguments = val_pop(a, 0);
    val* body = val_pop(a, 0);
    val_del(a);
    return val_lambda(arguments, body);
}

/**
 * Exit the program with status code given
 */
val* builtin_exit(env* e, val* a) {
    ASSERT_NUM("exit", a, 1);
    ASSERT_TYPE("exit", a, 0, VAL_NUM);
    // Should I free the memory here? not sure...
    exit(a->cell[0]->num);
}

/**
 * Print a symbol
 */
val* builtin_print(env* e, val* a) {
    for (int i = 0; i < a->count; i++) {
        val_print(a->cell[i]);
        putchar(' ');
    }
    putchar('\n');
    val_del(a);
    return val_pringle();
}

/**
 * Throw an error with the given message string
 */
val* builtin_error(env* e, val* a) {
    ASSERT_NUM("error", a, 1);
    ASSERT_TYPE("error", a, 0, VAL_STR);
    val* err = val_err(a->cell[0]->str);
    val_del(a);
    return err;
}

/**
 * Get the type of the given symbol
 */
val* builtin_type(env* e, val* a) {
    ASSERT_NUM("type", a, 1);
    val_del(a);
    return val_str(type_name(a->cell[0]->type));
}

val* load_file(env* e, char* path) {
    mpc_result_t r;
    if (mpc_parse_contents(path, Crisp, &r)) {
        val* expr = val_read(r.output);
        mpc_ast_delete(r.output);
        while (expr->count) {
            val* x = val_eval(e, val_pop(expr, 0));
            if (x->type == VAL_ERR) { val_println(x); }
            val_del(x);
        }
        val_del(expr);
        return val_pringle();
    } else {
        char* err_msg = mpc_err_string(r.error);
        mpc_err_delete(r.error);
        val* err = val_err("Could not open file %s", err_msg);
        free(err_msg);
        return err;
    }
}

/**
 * Load and evaluate an external file
 */
val* builtin_load(env* e, val* a) {
    ASSERT_NUM("load", a, 1);
    ASSERT_TYPE("load", a, 0, VAL_STR);
    val* result = load_file(e, a->cell[0]->str);
    val_del(a);
    return result;
}

void env_add_builtin(env* e, char* name, builtin func) {
    val* k = val_sym(name);
    val* v = val_fun(func);
    env_put(e, k, v);
    val_del(k);
    val_del(v);
}

void env_add_builtins(env* e) {
    // List functions
    env_add_builtin(e, "head", builtin_head);
    env_add_builtin(e, "tail", builtin_tail);
    env_add_builtin(e, "list", builtin_list);
    env_add_builtin(e, "eval", builtin_eval);
    env_add_builtin(e, "join", builtin_join);
    // Maths functions
    env_add_builtin(e, "+", builtin_add);
    env_add_builtin(e, "-", builtin_sub);
    env_add_builtin(e, "*", builtin_mul);
    env_add_builtin(e, "/", builtin_div);
    // Variable functions
    env_add_builtin(e, "def", builtin_def);
    env_add_builtin(e, "=", builtin_put);
    // Comparison functions
    env_add_builtin(e, "==", builtin_eq);
    env_add_builtin(e, "!=", builtin_ne);
    env_add_builtin(e, ">", builtin_gt);
    env_add_builtin(e, "<", builtin_lt);
    env_add_builtin(e, ">=", builtin_ge);
    env_add_builtin(e, "<=", builtin_le);
    // General functions
    env_add_builtin(e, "\\", builtin_lambda);
    env_add_builtin(e, "if", builtin_if);
    env_add_builtin(e, "load", builtin_load);
    env_add_builtin(e, "error", builtin_error);
    env_add_builtin(e, "print", builtin_print);
    env_add_builtin(e, "type", builtin_type);
    env_add_builtin(e, "exit", builtin_exit);
}

/*
 * Main
 */

int main(int argc, char** argv) {
    Number  = mpc_new("number");
    Symbol  = mpc_new("symbol");
    String  = mpc_new("string");
    Comment = mpc_new("comment");
    Pringle = mpc_new("pringle");
    List    = mpc_new("list");
    Expr    = mpc_new("expr");
    Crisp   = mpc_new("crisp");
    mpca_lang(MPCA_LANG_DEFAULT,
        "number  : /-?[0-9.]+/ ;"
        "symbol  : /[a-zA-Z0-9_+\\-*\\/\\\\=<>!&]+/ ;"
        "string  : /\"(\\\\.|[^\"])*\"/ ;"
        "comment : /;[^\\r\\n]*/ ;"
        "pringle : '(' <expr>* ')' ;"
        "list    : '{' <expr>* '}' ;"
        "expr    : <number> | <symbol> | <string>"
        "        | <comment> | <pringle> | <list> ;"
        "crisp   : /^/ <expr>* /$/ ;",
        Number, Symbol, String, Comment, Pringle, List, Expr, Crisp);
    env* e = env_new();
    env_add_builtins(e);
    if (argc == 1) {
        puts("Crisp 0.0.1");
        puts("To exit press Ctrl+C or enter 'exit 0'\n");
        while (1) {
            char *input = readline(">>> ");
            add_history(input);
            mpc_result_t r;
            if (mpc_parse("<stdin>", input, Crisp, &r)) {
                val* x = val_eval(e, val_read(r.output));
                val_println(x);
                val_del(x);
            } else {
                print_err("General parsing error\n");
            }
            free(input);
        }
    }
    if (argc >= 2) {
        for (int i = 1; i < argc; i++) {
            val* args = val_add(val_pringle(), val_str(argv[i]));
            val* x = builtin_load(e, args);
            if (x->type == VAL_ERR) { val_println(x); }
            val_del(x);
        }
    }
    env_del(e);
    mpc_cleanup(8,
        Number, Symbol, String, Comment,
        Pringle, List, Expr, Crisp);
    return 0;
}
