#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include <editline/readline.h>
#include "mpc.h"


struct lval;
struct lenv;
typedef struct lval lval;
typedef struct lenv lenv;

/* Value types */
enum ltype { LVAL_NUM, LVAL_ERR, LVAL_SYM, LVAL_FUN, LVAL_SEXPR, LVAL_QEXPR };

/* Builtin function pointer */
typedef lval*(*lbuiltin)(lenv*, lval*);

/* Value */
struct lval {
	int type;

	/* For basic values */
	long num;
	char* err;
	char* sym;

	/* For function values */
	lbuiltin builtin;
	lenv* env;
	lval* formals;
	lval* body;

	/* For expression values */
	int count;
	lval** cell;
};

/* Environment */
struct lenv {
	lenv* par;
	int count;
	char** syms;
	lval** vals;
};

char* ltype_name(int t) {
	switch(t) {
		case LVAL_FUN: return "Function";
		case LVAL_NUM: return "Number";
		case LVAL_ERR: return "Error";
		case LVAL_SYM: return "Symbol";
		case LVAL_SEXPR: return "S-Expression";
		case LVAL_QEXPR: return "Q-Expression";
		default: return "Unknown";
	}
}

/* Forward declarations */
lenv* lenv_new(void);
lval* lenv_get(lenv* e, lval* k);
void lenv_put(lenv* e, lval* k, lval* v);
lenv* lenv_copy(lenv* e);
void lenv_del(lenv* e);
void lenv_add_builtins(lenv* e);

lval* lval_eval(lenv* e, lval* v);
lval* lval_call(lenv* e, lval* f, lval* a);
void lval_print(lval* v);

lval* builtin_eval(lenv* e, lval* a);
lval* builtin_list(lenv* e, lval* a);

/* Create number value */
lval* lval_num(long x) {
	lval* v = malloc(sizeof(lval));
	v->type = LVAL_NUM;
	v->num = x;
	return v;
}

/* Create error value */
lval* lval_err(char* fmt, ...) {
	lval* v = malloc(sizeof(lval));
	v->type = LVAL_ERR;

	va_list va;
	va_start(va, fmt);

	v->err = malloc(512);
	vsnprintf(v->err, 511, fmt, va);
	v->err = realloc(v->err, strlen(v->err)+1);

	va_end(va);

	return v;
}

/* Create symbol value */
lval* lval_sym(char* s) {
	lval* v = malloc(sizeof(lval));
	v->type = LVAL_SYM;
	v->sym = malloc(strlen(s) + 1);
	strcpy(v->sym, s);
	return v;
}

/* Create S-Expression value */
lval* lval_sexpr(void) {
	lval* v = malloc(sizeof(lval));
	v->type = LVAL_SEXPR;
	v->count = 0;
	v->cell = NULL;
	return v;
}

/* Create Q-Expression value */
lval* lval_qexpr(void) {
	lval* v = malloc(sizeof(lval));
	v->type = LVAL_QEXPR;
	v->count = 0;
	v->cell = NULL;
	return v;
}

/* Create function value */
lval* lval_fun(lbuiltin func) {
	lval* v = malloc(sizeof(lval));
	v->type = LVAL_FUN;
	v->builtin = func;
	return v;
}

/* Create user defined function value */
lval* lval_lambda(lval* formals, lval* body) {
	lval* v = malloc(sizeof(lval));
	v->type = LVAL_FUN;
	v->builtin = NULL;
	v->env = lenv_new();
	v->formals = formals;
	v->body = body;

	return v;
}

/* Delete value */
void lval_del(lval* v) {
	switch (v->type) {
		case LVAL_NUM:
		break;

		case LVAL_FUN:
			if (!v->builtin) {
				lenv_del(v->env);
				lval_del(v->formals);
				lval_del(v->body);
			}
		break;

		case LVAL_ERR:
			free(v->err);
		break;

		case LVAL_SYM:
			free(v->sym);
		break;

		case LVAL_SEXPR:
		case LVAL_QEXPR:
			for (int i = 0; i < v->count; i++) {
				lval_del(v->cell[i]);
			}
			free(v->cell);
		break;
	}

	free(v);
}

/* Append value x to S/Q-Expression value v */
lval* lval_add(lval* v, lval* x) {
	v->count++;
	v->cell = realloc(v->cell, sizeof(lval*) * v->count);
	v->cell[v->count-1] = x;
	return v;
}

/* Create a number value from a parse tree node */
lval* lval_read_num(mpc_ast_t* t) {
	errno = 0;
	long x = strtol(t->contents, NULL, 10);
	return errno != ERANGE ? lval_num(x) : lval_err("Invalid number: %s", t->contents);
}


/* Create a value with the  appropriate type from a parse tree node */
lval* lval_read(mpc_ast_t* t) {
	if (strstr(t->tag, "number")) { return lval_read_num(t); }
	if (strstr(t->tag, "symbol")) { return lval_sym(t->contents); }

	lval* x = NULL;
	if (strcmp(t->tag, ">") == 0) { x = lval_sexpr(); }
	if (strstr(t->tag, "sexpr")) { x = lval_sexpr(); }
	if (strstr(t->tag, "qexpr")) { x = lval_qexpr(); }

	for (int i = 0; i < t->children_num; i++) {
		if (strcmp(t->children[i]->contents, "(") == 0) { continue; }
		if (strcmp(t->children[i]->contents, ")") == 0) { continue; }
		if (strcmp(t->children[i]->contents, "{") == 0) { continue; }
		if (strcmp(t->children[i]->contents, "}") == 0) { continue; }
		if (strcmp(t->children[i]->tag, "regex") == 0) { continue; }
		x = lval_add(x, lval_read(t->children[i]));
	}

	return x;
}

/* Print S/Q-expression */
void lval_expr_print(lval* v, char open, char close) {
	putchar(open);
	for (int i = 0; i < v->count; i++) {
		lval_print(v->cell[i]);

		if (i != (v->count - 1)) {
			putchar(' ');
		}
	}
	putchar(close);
}

/* Print a value */
void lval_print(lval* v) {
	switch (v->type) {
		case LVAL_NUM:
			printf("%li", v->num);
		break;

		case LVAL_FUN:
			if (v->builtin) {
				printf("<builtin>");
			} else {
				printf("(\\ ");
				lval_print(v->formals);
				putchar(' ');
				lval_print(v->body);
				putchar(')');
			}
		break;

		case LVAL_ERR:
			printf("Error: %s", v->err);
		break;

		case LVAL_SYM:
			printf("%s", v->sym);
		break;

		case LVAL_SEXPR:
			lval_expr_print(v, '(', ')');
		break;

		case LVAL_QEXPR:
			lval_expr_print(v, '{', '}');
		break;
	}
}

/* Print a value, followed by a newline */
void lval_println(lval* v) {
	lval_print(v); putchar('\n');
}

/* Remove and return the value at index i of S/Q-Expression v */
lval* lval_pop(lval* v, int i) {
	lval* x = v->cell[i];

	memmove(&v->cell[i], &v->cell[i+1], sizeof(lval*) * (v->count-i-1));
	v->count--;
	v->cell = realloc(v->cell, sizeof(lval*) * v->count);

	return x;
}

/* Insert the value x at index i of S/Q-Expression v */
lval* lval_insert(lval* v, lval* x, int i) {
	v->count++;
	v->cell = realloc(v->cell, sizeof(lval*) * v->count);
	memmove(&v->cell[i+1], &v->cell[i], sizeof(lval*) * (v->count-1-i));

	v->cell[i] = x;

	return v;
}


/* Return the value at index i of value v, delete original value */
lval* lval_take(lval *v, int i) {
	lval* x = lval_pop(v, i);
	lval_del(v);
	return x;
}

/* Append all cells of S/Q-Expression y to S/Q-Expression x, delete y */
lval* lval_join(lval* x, lval* y) {
	while (y->count) {
		x = lval_add(x, lval_pop(y, 0));
	}

	lval_del(y);
	return x;
}

/* Copy value */
lval* lval_copy(lval* v) {
	lval* x = malloc(sizeof(lval));
	x->type = v->type;

	switch (v->type) {
		case LVAL_NUM:
			x->num = v->num;
		break;

		case LVAL_FUN:
			if (v->builtin) {
				x->builtin = v->builtin;
			} else {
				x->builtin = NULL;
				x->env = lenv_copy(v->env);
				x->formals = lval_copy(v->formals);
				x->body = lval_copy(v->body);
			}
		break;

		case LVAL_ERR:
			x->err = malloc(strlen(v->err) + 1);
			strcpy(x->err, v->err);
		break;

		case LVAL_SYM:
			x->sym = malloc(strlen(v->sym) + 1);
			strcpy(x->sym, v->sym);
		break;

		case LVAL_SEXPR:
		case LVAL_QEXPR:
			x->count = v->count;
			x->cell = malloc(sizeof(lval*) * x->count);
			for (int i = 0; i < x->count; i++) {
				x->cell[i] = lval_copy(v->cell[i]);
			}
		break;
	}

	return x;
}

/* Evaluate S-Expression */
lval* lval_eval_sexpr(lenv* e, lval* v) {
	/* Evaluate all cells */
	for (int i = 0; i < v->count; i++) {
		v->cell[i] = lval_eval(e, v->cell[i]);
	}

	/* If any cell evaluated to an error, return the first one encountered */
	for (int i = 0; i < v->count; i++) {
		if (v->cell[i]->type == LVAL_ERR) { return lval_take(v, i); }
	}

	if (v->count == 0) { return v; }

	if (v->count == 1) { return lval_take(v, 0); }

	lval* f = lval_pop(v, 0);
	if (f->type != LVAL_FUN) {
		lval* err = lval_err("Expected first element to be a function, got %s", ltype_name(f->type));
		lval_del(f);
		lval_del(v);
		return err;
	}

	lval* result = lval_call(e, f, v);
	lval_del(f);

	return result;
}

/* Evaluate value */
lval* lval_eval(lenv* e, lval* v) {
	if (v->type == LVAL_SYM) {
		lval* x = lenv_get(e, v);
		lval_del(v);
		return x;
	}

	if (v->type == LVAL_SEXPR) {
		return lval_eval_sexpr(e, v);
	}

	return v;
}

int lval_eq(lval* x, lval* y) {
	if (x->type != x->type) { return 0; }

	switch (x->type) {
		case LVAL_NUM:
			return (x->num == y->num);
		break;

		case LVAL_ERR:
			return (strcmp(x->err, y->err) == 0);
		break;

		case LVAL_SYM:
			return (strcmp(x->sym, y->sym) == 0);
		break;

		case LVAL_FUN:
			if (x->builtin || y->builtin) {
				return x->builtin == y->builtin;
			} else {
				return lval_eq(x->formals, y->formals) && lval_eq(x->body, y->body);
			}
		break;

		case LVAL_QEXPR:
		case LVAL_SEXPR:
			if (x->count != y->count) { return 0; }

			for (int i = 0; i < x->count; i++) {
				if (!lval_eq(x->cell[i], y->cell[i])) { return 0; }
			}

			return 1;
		break;
	}
	return 0;
}

/* Call function or return a function with some parameters unbound, if there
   are less arguments than formals */
lval* lval_call(lenv* e, lval* f, lval* a) {
	if (f->builtin) {
		return f->builtin(e, a);
	}

	int given = a->count;
	int total = f->formals->count;

	while (a->count) {
		if (f->formals->count == 0) {
			lval_del(a);
			return lval_err(
				"Function passed too many arguments. Got %i, expected %i",
				given,
				total
			);
		}

		/* Get next formal and value. Note to self: we can carelessly consume the
		   function formals because we either defined it on the fly or we got a copy
		   by accessing a function in the env via lenv_get. */
		lval* sym = lval_pop(f->formals, 0);

		if (strcmp(sym->sym, "&") == 0) {
			/* We expect exactly one argument after "&" - the symbol which will hold
			   the variable arguments */
			if (f->formals->count != 1) {
				lval_del(a);
				return lval_err("Function format invalid. Symbol '&' not followed by single symbol.");
			}

			/* Put the rest of the parameters into the env */
			lval* nsym = lval_pop(f->formals, 0);
			lenv_put(f->env, nsym, builtin_list(e, a));

			lval_del(sym);
			lval_del(nsym);

			break;
		}
		lval* val = lval_pop(a, 0);

		lenv_put(f->env, sym, val);

		lval_del(sym);
		lval_del(val);
	}

	lval_del(a);

	if (f->formals->count == 0) {
		/* All formals have been bound, evaluate */
		f->env->par = e;
		return builtin_eval(f->env, lval_add(lval_sexpr(), lval_copy(f->body)));
	} else {
		/* Some parameters remain unbound, return partially bound function */
		return lval_copy(f);
	}
}

/* Create new environment */
lenv* lenv_new(void) {
	lenv* e = malloc(sizeof(lenv));

	e->par = NULL;
	e->count = 0;
	e->syms = NULL;
	e->vals = NULL;

	return e;
}

/* Delete given environment */
void lenv_del(lenv* e) {
	for (int i = 0; i < e->count; i++) {
		free(e->syms[i]);
		lval_del(e->vals[i]);
	}

	free(e->syms);
	free(e->vals);
	free(e);
}

/* Copy given environment */
lenv* lenv_copy(lenv* e) {
	lenv* n = lenv_new();

	n->par = e->par;
	n->count = e->count;
	n->syms = malloc(sizeof(char*) * n->count);
	n->vals = malloc(sizeof(lval*) * n->count);

	for (int i=0; i < e->count; i++) {
		n->syms[i] = malloc(strlen(e->syms[i])+1);
		strcpy(n->syms[i], e->syms[i]);

		n->vals[i] = lval_copy(e->vals[i]);
	}

	return n;
}

/* Get value from environment for the given symbol */
lval* lenv_get(lenv* e, lval* k) {
	for (int i = 0; i < e->count; i++) {
		if (strcmp(e->syms[i], k->sym) == 0) {
			return lval_copy(e->vals[i]);
		}
	}

	if (e->par) {
		return lenv_get(e->par, k);
	} else {
		return lval_err("Unbound symbol '%s'", k->sym);
	}
}

/* Put a value for the given symbol into the environment */
void lenv_put(lenv* e, lval* k, lval* v) {
	for (int i = 0; i < e->count; i++) {
		if (strcmp(e->syms[i], k->sym) == 0) {
			/* Symbol is already in the environment, replace it */
			lval_del(e->vals[i]);
			e->vals[i] = lval_copy(v);
			return;
		}
	}

	/* Symbol is not in the environment, add it */
	e->count++;
	e->vals = realloc(e->vals, sizeof(lval*) * e->count);
	e->syms = realloc(e->syms, sizeof(char*) * e->count);

	e->syms[e->count-1] = malloc(strlen(k->sym)+1);
	strcpy(e->syms[e->count-1], k->sym);
	e->vals[e->count-1] = lval_copy(v);
}


/* Set value in the topmost parent environment of the given environment */
void lenv_def(lenv* e, lval* k, lval* v) {
	while (e->par) (e = e->par);
	lenv_put(e, k, v);
}

/* Print all symbols and values in the environment */
void lenv_print(lenv* e) {
	for (int i=0; i<e->count; i++) {
		printf("%s = ", e->syms[i]);
		lval_println(e->vals[i]);
	}
}

/* Add builtin function to environment */
void lenv_add_builtin(lenv* e, char* name, lbuiltin func) {
	lval* k = lval_sym(name);
	lval* v = lval_fun(func);

	lenv_put(e, k, v);

	lval_del(k);
	lval_del(v);
}

#define LASSERT(args, cond, fmt, ...) \
	if (!(cond)) { \
		lval* err = lval_err(fmt, ##__VA_ARGS__); \
		lval_del(args); \
		return err; \
	}
#define LASSERT_NOT_EMPTY(args, err) if (args->cell[0]->count == 0) \
	{ lval_del(args); return lval_err(err); }

#define LASSERT_NUM(fn, args, c) if (args->count != c) \
	{ \
		int actual_count = args->count; \
		lval_del(args); \
		return lval_err( \
			"Wrong argument count for function '%s' expected %i, got %i", \
			fn, c, actual_count \
		); \
	};

#define LASSERT_TYPE(fn, args, i, t) if (args->cell[i]->type != t) \
	{ \
		enum ltype actual_type = args->cell[i]->type; \
		lval_del(args); \
		return lval_err( \
			"Wrong type for argument %i of function %s: expected %s, got %s", \
			i, fn, ltype_name(t), ltype_name(actual_type) \
		); \
	};

/* Math operations */
lval* builtin_op(lenv* e, lval* a, char* op) {
	for (int i = 0; i < a->count; i++) {
		if (a->cell[i]->type != LVAL_NUM) {
			lval* err = lval_err(
				"Wrong type for function '%s' parameter %i: expected number, got %s",
				op,
				i,
				ltype_name(a->cell[i]->type)
			);
			lval_del(a);
			return err;
		}
	}

	lval* x = lval_pop(a, 0);

	if (strcmp(op, "-") == 0 && a->count == 0) { x->num = -x->num; }

	while (a->count > 0) {
		lval* y = lval_pop(a, 0);

		if (strcmp(op, "+") == 0) { x->num += y->num; }
		if (strcmp(op, "-") == 0) { x->num -= y->num; }
		if (strcmp(op, "*") == 0) { x->num *= y->num; }
		if (strcmp(op, "/") == 0) {
			if (y->num == 0) {
				lval_del(x);
				lval_del(y);
				x = lval_err("Division by zero!");
				break;
			}
			x->num /= y->num;
		}

		lval_del(y);
	}

	lval_del(a);
	return x;
}

/* builtin_op wrapper for "+" */
lval* builtin_add(lenv* e, lval* a) {
	return builtin_op(e, a, "+");
}

/* builtin_op wrapper for "-" */
lval* builtin_sub(lenv* e, lval* a) {
	return builtin_op(e, a, "-");
}

/* builtin_op wrapper for "*" */
lval* builtin_mul(lenv* e, lval* a) {
	return builtin_op(e, a, "*");
}

/* builtin_op wrapper for "/" */
lval* builtin_div(lenv* e, lval* a) {
	return builtin_op(e, a, "/");
}

/* Compares two number values, returns 0 for false and 1 for true */
lval* builtin_ord(lenv* e, lval* a, char* op) {
	LASSERT_NUM(op, a, 2);
	LASSERT_TYPE(op, a, 0, LVAL_NUM);
	LASSERT_TYPE(op, a, 1, LVAL_NUM);

	lval* r = lval_num(0);

	long left = a->cell[0]->num;
	long right = a->cell[1]->num;

	if (strcmp(op, ">") == 0) { r->num = left > right; }
	if (strcmp(op, "<") == 0) { r->num = left < right; }
	if (strcmp(op, ">=") == 0) { r->num = left >= right; }
	if (strcmp(op, "<=") == 0) { r->num = left <= right; }

	lval_del(a);
	return r;
}

/* builtin_ord wrapper for ">" */
lval* builtin_gt(lenv* e, lval* a) {
	return builtin_ord(e, a, ">");
}

/* builtin_ord wrapper for "<" */
lval* builtin_lt(lenv* e, lval* a) {
	return builtin_ord(e, a, "<");
}

/* builtin_ord wrapper for ">=" */
lval* builtin_gte(lenv* e, lval* a) {
	return builtin_ord(e, a, ">=");
}

/* builtin_ord wrapper for "<=" */
lval* builtin_lte(lenv* e, lval* a) {
	return builtin_ord(e, a, "<=");
}

/* Compares any two values for equality/non-equality */
lval* builtin_cmp(lenv* e, lval* a, char* op) {
	LASSERT_NUM(op, a, 2);

	lval* r = lval_num(0);
	if (strcmp(op, "==") == 0) { r->num = lval_eq(a->cell[0], a->cell[1]); }
	if (strcmp(op, "!=") == 0) { r->num = !lval_eq(a->cell[1], a->cell[1]); }

	lval_del(a);
	return r;
}

/* builtin_cmp wrapper for "==" */
lval* builtin_eq(lenv* e, lval* a) {
	return builtin_cmp(e, a, "==");
}

/* builtin_cmp wrapper for "!=" */
lval* builtin_ne(lenv* e, lval* a) {
	return builtin_cmp(e, a, "!=");
}

/* Logical NOT */
lval* builtin_not(lenv* e, lval* a) {
	LASSERT_NUM('!', a, 1);
	LASSERT_TYPE('!', a, 0, LVAL_NUM);

	lval* r = lval_num(!a->cell[0]->num);
	lval_del(a);

	return r;
}

/* Boolean operations */
lval* builtin_bool(lenv* e, lval* a, char* op) {
	LASSERT(a, (a->count > 1), "Need at least 2 arguments for function %s, got %i", op, a->count);
	for (int i = 0; i < a->count; i++) {
		LASSERT_TYPE(op, a, i, LVAL_NUM);
	}

	lval* x = lval_pop(a, 0);

	while (a->count) {
		/* Short circuit checks */
		if (strcmp(op, "&&") == 0 && !x->num) { break; }
		if (strcmp(op, "||") == 0 && x->num) { break; }

		/* Process next operand */
		lval* y = lval_pop(a, 0);

		if (strcmp(op, "&&") == 0) { x->num = x->num && y->num; }
		if (strcmp(op, "&&") == 0) { x->num = x->num || y->num; }

		lval_del(y);
	}

	lval_del(a);
	return x;
}

/* Boolean AND */
lval* builtin_and(lenv* e, lval* a) {
	return builtin_bool(e, a, "&&");
}

/* Boolean OR */
lval* builtin_or(lenv* e, lval* a) {
	return builtin_bool(e, a, "||");
}

/* Define symbol(s) */
lval* builtin_var(lenv* e, lval* a, char* func) {
	LASSERT_TYPE(func, a, 0, LVAL_QEXPR);

	lval* syms = a->cell[0];

	/* Check that all items in the symbol list are symbols */
	for (int i=0; i < syms->count; i++) {
		LASSERT(
			a,
			(syms->cell[i]->type == LVAL_SYM),
			"Function '%s' cannot define non-symbol. Expected %s, got %s.",
			func, ltype_name(LVAL_SYM), ltype_name(syms->cell[i]->type)
		);
	}

	/* Check that symbol and value count match */
	LASSERT(
		a,
		(syms->count == a->count-1),
		"Function '%s' symbol count doesn't match value count. Got %i values for %i symbols",
		func, a->count-1, syms->count
	);

	/* Assign values to symbols */
	for (int i=0; i < syms->count; i++) {
		if (strcmp(func, "def") == 0) { lenv_def(e, syms->cell[i], a->cell[i+1]); };
		if (strcmp(func, "=") == 0) { lenv_put(e, syms->cell[i], a->cell[i+1]); };
	}

	lval_del(a);

	return lval_sexpr();
}

lval* builtin_def(lenv* e, lval* a) {
	return builtin_var(e, a, "def");
}

lval* builtin_put(lenv* e, lval* a) {
	return builtin_var(e, a, "=");
}

/* Return first element of the given Q-Expression */
lval* builtin_head(lenv* e, lval* a) {
	LASSERT_NUM("head", a, 1)
	LASSERT_NOT_EMPTY(a, "Function 'head' got passed {}")
	LASSERT(
		a,
		(a->cell[0]->type == LVAL_QEXPR),
		"Function 'head' passed incorrect type for argument 0. Got %s, expected %s.",
		ltype_name(a->cell[0]->type), ltype_name(LVAL_QEXPR)
	);

	lval* v = lval_take(a, 0);
	while (v->count > 1) {
		lval_del(lval_pop(v, 1));
	}

	return v;
}

/* Return the Q-Expression with the first element removed */
lval* builtin_tail(lenv* e, lval* a) {
	LASSERT_NOT_EMPTY(a, "Function 'tail' passed {}!");
	LASSERT_NUM("tail", a, 1);
	LASSERT(a, (a->cell[0]->type == LVAL_QEXPR), "Function 'tail' passed incorrect types!");

	lval* v = lval_take(a, 0);
	lval_del(lval_pop(v, 0));

	return v;
}

/* Return Q-Expression with the arguments as items */
lval* builtin_list(lenv* e, lval* a) {
	a->type = LVAL_QEXPR;
	return a;
}

/* Join contents of argument Q-Expressions into single Q-Expression */
lval* builtin_join(lenv* e, lval* a) {
	for (int i = 0; i < a->count; i++) {
		LASSERT(a, (a->cell[i]->type == LVAL_QEXPR), "Function 'join' passed incorrect type.");
	}

	lval* x = lval_pop(a, 0);

	while (a->count) {
		x = lval_join(x, lval_pop(a, 0));
	}

	lval_del(a);
	return x;
}

/* Evaluate the given Q-Expression as S-Expression */
lval* builtin_eval(lenv* e, lval* a) {
	LASSERT(a, (a->count == 1), "Function 'eval' passed too many arguments!");
	LASSERT(a, (a->cell[0]->type == LVAL_QEXPR), "Function 'eval' passed incorrect type!");

	lval* x = lval_take(a, 0);
	x->type = LVAL_SEXPR;
	return lval_eval(e, x);
}

/* Return the given Q-Expression with the given value inserted at its beginning */
lval* builtin_cons(lenv* e, lval* a) {
	LASSERT(a, (a->count <= 2), "Function 'cons' passed too many arguments!");
	LASSERT(a, (a->count >= 2), "Function 'cons' passed too few arguments!");
	LASSERT(a, (a->cell[1]->type == LVAL_QEXPR), "Function 'eval' expects a qexpr as second argument!");

	lval* x = lval_pop(a, 0);
	a = lval_pop(a, 0);
	lval_insert(a, x, 0);

	return a;
}

/* Return the length of the given Q-Expression */
lval* builtin_len(lenv* e, lval* a) {
	LASSERT_NUM("len", a, 1);
	LASSERT(a, (a->cell[0]->type == LVAL_QEXPR), "Function 'eval' passed incorrect type!");

	int count = a->cell[0]->count;
	lval_del(a);

	return lval_num(count);
}

/* Return the given Q-Expression with its last element removed */
lval* builtin_init(lenv* e, lval* a) {
	LASSERT_NOT_EMPTY(a, "Function 'tail' passed {}!");
	LASSERT_NUM("init", a, 1);
	LASSERT(a, (a->cell[0]->type == LVAL_QEXPR), "Function 'init' passed incorrect type!");

	lval_del(lval_pop(a->cell[0], a->cell[0]->count-1));
	return lval_take(a, 0);
}

/* Print contents of the environment */
lval* builtin_dump(lenv* e, lval* a) {
	/* We allow any number of parameters, because there is now way
	to call a function without parameters right now, todo */
	lval_del(a);

	lenv_print(e);

	return lval_sexpr();
}

/* Set run_interpreter variable to 0, signalling that the program should exit */
lval* builtin_exit(lenv* e, lval* a) {
	/* We allow any number of parameters, because there is now way
	to call a function without parameters right now, todo */
	lval_del(a);

	lenv_put(e, lval_sym("run_interpreter"), lval_num(0));

	return lval_sexpr();
}

/* Define new function */
lval* builtin_lambda(lenv* e, lval* a) {
	/* Expecting two Q-Expr arguments - the formals and body of the function */
	LASSERT_NUM("\\", a, 2);
	LASSERT_TYPE("\\", a, 0, LVAL_QEXPR);
	LASSERT_TYPE("\\", a, 1, LVAL_QEXPR);

	/* Check that formals contains only symbols */
	for (int i = 0; i<a->cell[0]->count; i++) {
		LASSERT(
			a,
			(a->cell[0]->cell[i]->type == LVAL_SYM),
			"Cannot define non-symbol: got %s, expected %s.",
			ltype_name(a->cell[0]->cell[i]->type), ltype_name(LVAL_SYM)
		);
	}

	lval* formals = lval_pop(a, 0);
	lval* body = lval_pop(a, 0);
	lval_del(a);

	return lval_lambda(formals, body);
}

/* Choose code to evaluate depending on a condition */
lval* builtin_if(lenv* e, lval* a) {
	/* Expecting 3 parameters: condition, true-code, false-code */
	LASSERT_NUM("if", a, 3);
	LASSERT_TYPE("if", a, 0, LVAL_NUM);
	LASSERT_TYPE("if", a, 1, LVAL_QEXPR);
	LASSERT_TYPE("if", a, 2, LVAL_QEXPR);

	lval* x = NULL;
	if (a->cell[0]-> num == 0) {
		x = lval_take(a, 2);
	} else {
		x = lval_take(a, 1);
	}

	x->type = LVAL_SEXPR;
	return lval_eval(e, x);
}

/* Add builtin functions to an environment */
void lenv_add_builtins(lenv* e) {
	lenv_add_builtin(e, "\\", builtin_lambda);
	lenv_add_builtin(e, "if", builtin_if);
	lenv_add_builtin(e, "def", builtin_def);
	lenv_add_builtin(e, "=", builtin_put);
	lenv_add_builtin(e, "dump", builtin_dump);
	lenv_add_builtin(e, "exit", builtin_exit);

	/* List functions */
	lenv_add_builtin(e, "list", builtin_list);
	lenv_add_builtin(e, "len", builtin_len);
	lenv_add_builtin(e, "init", builtin_init);
	lenv_add_builtin(e, "head", builtin_head);
	lenv_add_builtin(e, "tail", builtin_tail);
	lenv_add_builtin(e, "join", builtin_join);
	lenv_add_builtin(e, "cons", builtin_cons);
	lenv_add_builtin(e, "eval", builtin_eval);

	/* Math functions */
	lenv_add_builtin(e, "+", builtin_add);
	lenv_add_builtin(e, "-", builtin_sub);
	lenv_add_builtin(e, "*", builtin_mul);
	lenv_add_builtin(e, "/", builtin_div);

	/* Number comparison functions */
	lenv_add_builtin(e, ">", builtin_gt);
	lenv_add_builtin(e, "<", builtin_lt);
	lenv_add_builtin(e, ">=", builtin_gte);
	lenv_add_builtin(e, "<=", builtin_lte);

	/* Equality test functions */
	lenv_add_builtin(e, "==", builtin_eq);
	lenv_add_builtin(e, "!=", builtin_ne);

	/* Boolean functions */
	lenv_add_builtin(e, "!", builtin_not);
	lenv_add_builtin(e, "||", builtin_or);
	lenv_add_builtin(e, "&&", builtin_and);
}

int main(int argc, char** argv) {
	mpc_parser_t* Number = mpc_new("number");
	mpc_parser_t* Symbol = mpc_new("symbol");
	mpc_parser_t* Sexpr = mpc_new("sexpr");
	mpc_parser_t* Qexpr = mpc_new("qexpr");
	mpc_parser_t* Expr = mpc_new("expr");
	mpc_parser_t* Lispy = mpc_new("lispy");

	puts("Declared parsers");

	mpca_lang(MPC_LANG_DEFAULT,
		"                                                       \
			number : /-?[0-9]+/ ;                               \
			symbol : /[a-zA-Z0-9_+\\-*\\/\\\\=<>!&|]+/ ;        \
			sexpr  : '(' <expr>* ')' ;                          \
			qexpr  : '{' <expr>* '}' ;                          \
			expr   : <number> | <symbol> | <sexpr> | <qexpr> ;  \
			lispy  : /^/ <expr>* /$/ ;                          \
		",
		Number, Symbol, Sexpr, Qexpr, Expr, Lispy);

	puts("Parsed parsers");

	lenv* e = lenv_new();
	lenv_add_builtins(e);
	lenv_put(e, lval_sym("run_interpreter"), lval_num(1));

	puts("Krispy version 0.0.0.0.1");
	puts("Press Ctrl+C to Exit\n");

	while (lenv_get(e, lval_sym("run_interpreter"))->num) {
		char* input = readline("krispy> ");
		add_history(input);

		mpc_result_t r;
		if (mpc_parse("<stdin>", input, Lispy, &r)) {
			lval* x = lval_eval(e, lval_read(r.output));
			lval_println(x);
			lval_del(x);

			mpc_ast_delete(r.output);
		} else {
			mpc_err_print(r.error);
			mpc_err_delete(r.error);
		}

		free(input);
	}

	lenv_del(e);

	mpc_cleanup(6, Number, Symbol, Sexpr, Qexpr, Expr, Lispy);

	puts("Exiting");
	return 0;
}
