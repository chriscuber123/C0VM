/**************************************************************************/
/*              COPYRIGHT Carnegie Mellon University 2022                 */
/* Do not post this file or any derivative on a public site or repository */
/**************************************************************************/
#include <assert.h>
#include <stdio.h>
#include <limits.h>
#include <stdlib.h>

#include "lib/xalloc.h"
#include "lib/stack.h"
#include "lib/contracts.h"
#include "lib/c0v_stack.h"
#include "lib/c0vm.h"
#include "lib/c0vm_c0ffi.h"
#include "lib/c0vm_abort.h"

/* call stack frames */
typedef struct frame_info frame;
struct frame_info {
  c0v_stack_t S;   /* Operand stack of C0 values */
  ubyte *P;        /* Function body */
  size_t pc;       /* Program counter */
  c0_value *V;     /* The local variables */
};

void push_int(c0v_stack_t S, int x)
{
  c0v_push(S, int2val(x));
}

int pop_int(c0v_stack_t S)
{
  return val2int(c0v_pop(S));
}

void push_ptr(c0v_stack_t S, void *x)
{
  c0v_push(S, ptr2val(x));
}

void *pop_ptr(c0v_stack_t S)
{
  return val2ptr(c0v_pop(S));
}

void push_taggedptr(c0v_stack_t S, void *x, uint16_t tag) {
  c0v_push(S, tagged_ptr2val(x, tag));
}

void *pop_taggedptr(c0v_stack_t S) {
  return val2tagged_ptr(c0v_pop(S));
}

int execute(struct bc0_file *bc0) {
  REQUIRES(bc0 != NULL);

  /* Variables */
  c0v_stack_t S; /* Operand stack of C0 values */
  ubyte *P;      /* Array of bytes that make up the current function */
  size_t pc;     /* Current location within the current byte array P */
  c0_value *V;   /* Local variables (you won't need this till Task 2) */
  (void) V;         // silences compilation errors about V being currently unused

  S = c0v_stack_new();
  P = bc0->function_pool[0].code;
  pc = 0;
  V = xcalloc(sizeof(c0_value), bc0->function_pool[0].num_vars);

  /* The call stack, a generic stack that should contain pointers to frames */
  /* You won't need this until you implement functions. */
  gstack_t callStack;
  (void) callStack; // silences compilation errors about callStack being currently unused
  callStack = stack_new();

  while (true) {

#ifdef DEBUG
    /* You can add extra debugging information here */
    fprintf(stderr, "Opcode %x -- Stack size: %zu -- PC: %zu\n",
            P[pc], c0v_stack_size(S), pc);
#endif

    switch (P[pc]) {

    /* Additional stack operation: */

    case POP: {
      pc++;
      c0v_pop(S);
      break;
    }

    case DUP: {
      pc++;
      c0_value v = c0v_pop(S);
      c0v_push(S, v);
      c0v_push(S, v);
      break;
    }

    case SWAP: {
      pc++;
      c0_value v1 = c0v_pop(S);
      c0_value v2 = c0v_pop(S);
      c0v_push(S, v1);
      c0v_push(S, v2);
      break;
    }


    /* Returning from a function.
     * This currently has a memory leak! You will need to make a slight
     * change for the initial tasks to avoid leaking memory.  You will
     * need to revise it further when you write INVOKESTATIC. */

    case RETURN: {
      c0_value retval = c0v_pop(S);
      assert(c0v_stack_empty(S));
// Another way to print only in DEBUG mode
// IF_DEBUG(fprintf(stderr, "Returning %d from execute()\n", retval));
      // Free everything before returning from the execute function!
      c0v_stack_free(S);
      free(V);
      if (stack_empty(callStack)) {
        stack_free(callStack, NULL);
        return val2int(retval);
      } else {
        frame *F = (frame*)pop(callStack);
        S = F->S;
        P = F->P;
        pc = F->pc;
        V = F->V;
        free(F);
        c0v_push(S, retval);
        break;
      }
    }


    /* Arithmetic and Logical operations */

    case IADD: {
      pc++;
      int v1 = pop_int(S);
      int v2 = pop_int(S);
      push_int(S, v2+v1);
      break;
    }

    case ISUB: {
      pc++;
      int v1 = pop_int(S);
      int v2 = pop_int(S);
      push_int(S, v2-v1);
      break;
    }

    case IMUL: {
      pc++;
      int v1 = pop_int(S);
      int v2 = pop_int(S);
      push_int(S, v2*v1);
      break;
    }

    case IDIV: {
      pc++;
      int v1 = pop_int(S);
      int v2 = pop_int(S);
      if (v1 == 0) c0_arith_error("Divide by 0 error\n");
      else if (v2 == INT_MIN && v1 == -1) c0_arith_error("Divide INT_MIN by -1 error\n");
      else push_int(S, v2/v1);
      break;
    }

    case IREM: {
      pc++;
      int v1 = pop_int(S);
      int v2 = pop_int(S);
      if (v1 == 0) c0_arith_error("Divide by 0 error\n");
      else if (v2 == INT_MIN && v1 == -1) c0_arith_error("Divide INT_MIN by -1 error\n");
      else push_int(S, v2%v1);
      break;
    }

    case IAND: {
      pc++;
      int v1 = pop_int(S);
      int v2 = pop_int(S);
      push_int(S, v2&v1);
      break;
    }

    case IOR: {
      pc++;
      int v1 = pop_int(S);
      int v2 = pop_int(S);
      push_int(S, v2|v1);
      break;
    }

    case IXOR: {
      pc++;
      int v1 = pop_int(S);
      int v2 = pop_int(S);
      push_int(S, v2^v1);
      break;
    }

    case ISHR: {
      pc++;
      int v1 = pop_int(S);
      int v2 = pop_int(S);
      if (v1 < 0) c0_arith_error("Cannot shift by negative amount\n");
      else if (v1 >= 32) c0_arith_error("Cannot shift more than 32 bits\n");
      else push_int(S, v2>>v1);
      break;
    }

    case ISHL: {
      pc++;
      int v1 = pop_int(S);
      int v2 = pop_int(S);
      if (v1 < 0) c0_arith_error("Cannot shift by negative amount\n");
      else if (v1 >= 32) c0_arith_error("Cannot shift more than 32 bits\n");
      else push_int(S, v2<<v1);
      break;
    }


    /* Pushing constants */

    case BIPUSH: {
      pc++;
      push_int(S, (int)(int8_t)P[pc]);
      pc++;
      break;
    }

    case ILDC: {
      pc++;
      uint32_t index = ((uint32_t)P[pc]) << 8;
      pc++;
      index |= (uint32_t)P[pc];
      push_int(S, bc0->int_pool[index]);
      pc++;
      break;
    }

    case ALDC: {
      pc++;
      uint32_t index = ((uint32_t)P[pc]) << 8;
      pc++;
      index |= (uint32_t)P[pc];
      push_ptr(S, (void*)&bc0->string_pool[index]);
      pc++;
      break;
    }

    case ACONST_NULL: {
      pc++;
      push_ptr(S, NULL);
      break;
    }


    /* Operations on local variables */

    case VLOAD: {
      pc++;
      c0v_push(S, V[P[pc]]);
      pc++;
      break;
    }

    case VSTORE: {
      pc++;
      V[P[pc]] = c0v_pop(S);
      pc++;
      break;
    }


    /* Assertions and errors */

    case ATHROW: {
      pc++;
      c0_user_error((char*)pop_ptr(S));
      break;
    }

    case ASSERT: {
      pc++;
      char *msg = (char*)pop_ptr(S);
      if (pop_int(S) == 0) c0_assertion_failure(msg);
      break;
    }


    /* Control flow operations */

    case NOP: {
      pc++;
      break;
    }

    case IF_CMPEQ: {
      pc++;
      if (val_equal(c0v_pop(S), c0v_pop(S))) {
        uint32_t tmp = (uint32_t)(P[pc]) << 8;
        pc++;
        tmp |= (uint32_t)P[pc];
        int32_t index = (int32_t)tmp;
        pc += index - 2;
        break;
      } else pc += 2;
      break;
    }

    case IF_CMPNE: {
      pc++;
      if (!val_equal(c0v_pop(S), c0v_pop(S))) {
        uint32_t tmp = (uint32_t)(P[pc]) << 8;
        pc++;
        tmp |= (uint32_t)P[pc];
        int32_t index = (int32_t)tmp;
        pc += index - 2;
        break;
      } else pc += 2;
      break;
    }

    case IF_ICMPLT: {
      pc++;
      if (pop_int(S) > pop_int(S)) {
        uint32_t tmp = (uint32_t)(P[pc]) << 8;
        pc++;
        tmp |= (uint32_t)P[pc];
        int32_t index = (int32_t)tmp;
        pc += index - 2;
        break;
      } else pc += 2;
      break;
    }

    case IF_ICMPGE: {
      pc++;
      if (pop_int(S) <= pop_int(S)) {
        uint32_t tmp = (uint32_t)(P[pc]) << 8;
        pc++;
        tmp |= (uint32_t)P[pc];
        int32_t index = (int32_t)tmp;
        pc += index - 2;
        break;
      } else pc += 2;
      break;
    }

    case IF_ICMPGT: {
      pc++;
      if (pop_int(S) < pop_int(S)) {
        uint32_t tmp = (uint32_t)(P[pc]) << 8;
        pc++;
        tmp |= (uint32_t)P[pc];
        int32_t index = (int32_t)tmp;
        pc += index - 2;
        break;
      } else pc += 2;
      break;
    }

    case IF_ICMPLE: {
      pc++;
      if (pop_int(S) >= pop_int(S)) {
        uint32_t tmp = (uint32_t)(P[pc]) << 8;
        pc++;
        tmp |= (uint32_t)P[pc];
        int32_t index = (int32_t)tmp;
        pc += index - 2;
        break;
      } else pc += 2;
      break;
    }

    case GOTO: {
      pc++;
      uint16_t tmp = (uint16_t)(P[pc]) << 8;
      pc++;
      tmp |= (uint16_t)P[pc];
      int16_t index = (int16_t)tmp;
      pc += index - 2;
      break;
    }


    /* Function call operations: */

    case INVOKESTATIC: {
      pc++;
      uint16_t tmp = (uint16_t)(P[pc]) << 8;
      pc++;
      tmp |= (uint16_t)P[pc];
      int16_t index = (int16_t)tmp;
      pc++;

      frame *F = xmalloc(sizeof(frame));
      F->S = S;
      F->P = P;
      F->pc = pc;
      F->V = V;
      push(callStack, (void*)F);

      struct function_info *f = &bc0->function_pool[index];
      int num_vars = (int)f->num_vars;
      int num_args = (int)f->num_args;

      V = xcalloc(sizeof(c0_value), num_vars);
      for (int i = num_args - 1; i >= 0; i--) {
        V[i] = c0v_pop(S);
      }

      S = c0v_stack_new();
      P = f->code;
      pc = 0;
      break;
    }

    case INVOKENATIVE: {
      pc++;
      uint16_t tmp = (uint16_t)(P[pc]) << 8;
      pc++;
      tmp |= (uint16_t)P[pc];
      int16_t index = (int16_t)tmp;

      struct native_info *f = &bc0->native_pool[index];
      int num_args = (int)f->num_args;
      
      c0_value *A = xcalloc(sizeof(c0_value), num_args);
      for (int i = num_args - 1; i >= 0; i--) {
        A[i] = c0v_pop(S);
      }

      uint16_t f_index = f->function_table_index;
      c0_value res = (*(native_function_table[f_index]))(A);
      c0v_push(S, res);
      pc++;
      break;
    }


    /* Memory allocation and access operations: */

    case NEW: {
      pc++;
      int s = (int)(int8_t)P[pc];
      void *ptr = xmalloc(sizeof(s));
      push_ptr(S, ptr);
      pc++;
      break;
    }

    case IMLOAD: {
      int *a = (int*)pop_ptr(S);
      if (a == NULL) c0_memory_error("Cannot have NULL pointer");
      push_int(S, *a);
      pc++;
      break;
    }

    case IMSTORE: {
      int x = pop_int(S);
      int *a = (int*)pop_ptr(S);
      if (a == NULL) c0_memory_error("Cannot have NULL pointer");
      *a = x;
      pc++;
      break;
    }

    case AMLOAD: {
      void **a = pop_ptr(S);
      if (a == NULL) c0_memory_error("Cannot have NULL pointer");
      void *b = *a;
      push_ptr(S, b);
      pc++;
      break;
    }

    case AMSTORE: {
      void *b = pop_ptr(S);
      void **a = pop_ptr(S);
      if (a == NULL) c0_memory_error("Cannot have NULL pointer");
      *a = b;
      pc++;
      break;
    }

    case CMLOAD: {
      char *a = (char*)pop_ptr(S);
      if (a == NULL) c0_memory_error("Cannot have NULL pointer");
      int x = (int)(int32_t)*a;
      push_int(S, x);
      pc++;
      break;
    }

    case CMSTORE: {
      int x = pop_int(S);
      char *a = (char*)pop_ptr(S);
      if (a == NULL) c0_memory_error("Cannot have NULL pointer");
      *a = x & 0x7f;
      pc++;
      break;
    }

    case AADDF: {
      pc++;
      ubyte f = (ubyte)P[pc];
      char *a = (char*)pop_ptr(S);
      if (a == NULL) c0_memory_error("Cannot have NULL pointer");
      push_ptr(S, (void*)(a+f));
      pc++;
      break;
    }


    /* Array operations: */

    case NEWARRAY: {
      pc++;
      int elt_size = (int)(int8_t)P[pc];
      int n = pop_int(S);
      c0_array *a = xmalloc(sizeof(c0_array));
      a->count = n;
      a->elt_size = elt_size;
      a->elems = xcalloc(sizeof(void*), n);
      push_ptr(S, (void*)a);
      pc++;
      break;
    }

    case ARRAYLENGTH: {
      c0_array *a = (c0_array*)pop_ptr(S);
      if (a == NULL) c0_memory_error("Cannot have NULL pointer");
      push_int(S, a->count);
      pc++;
      break;
    }

    case AADDS: {
      int i = pop_int(S);
      c0_array *a = (c0_array*)pop_ptr(S);
      if (a == NULL) c0_memory_error("Cannot have NULL pointer");
      if (i < 0 || i >= a->count) c0_memory_error("Index out of bounds");
      char *elems = (char*)a->elems;
      void *res = elems + (a->elt_size * i);
      push_ptr(S, res);
      pc++;
      break;
    }


    /* BONUS -- C1 operations */

    case CHECKTAG: {
      pc++;
      uint16_t tag = (uint16_t)(P[pc]) << 8;
      pc++;
      tag |= (uint16_t)P[pc];
      pc++;

      c0_tagged_ptr *a = (c0_tagged_ptr*)pop_taggedptr(S);
      if (a == NULL) c0_memory_error("Cannot have NULL pointer");
      else if (a->tag != tag) c0_memory_error("Incorrect tag");
      else {
        c0_value res = tagged_ptr2val((void*)a, tag);
        c0v_push(S, res);
        pc++;
        break;
      }
      break;
    }

    case HASTAG: {
      pc++;
      uint16_t tag = (uint16_t)(P[pc]) << 8;
      pc++;
      tag |= (uint16_t)P[pc];
      pc++;

      c0_tagged_ptr *a = (c0_tagged_ptr*)pop_taggedptr(S);
      if (a == NULL || a->tag != tag) push_int(S, (uint32_t)0);
      else push_int(S, (uint32_t)1);
      pc++;
      break;
    }

    case ADDTAG: {
      pc++;
      uint16_t tag = (uint16_t)(P[pc]) << 8;
      pc++;
      tag |= (uint16_t)P[pc];
      pc++;

      void *a = pop_ptr(S);
      c0_tagged_ptr *res = val2tagged_ptr(*(c0_value*)a);
      res->tag = tag;
      push_taggedptr(S, res, tag);
      pc++;
      break;
    }

    case ADDROF_STATIC: {
      pc++;
      uint16_t tmp = (uint16_t)(P[pc]) << 8;
      pc++;
      tmp |= (uint16_t)P[pc];
      int16_t index = (int16_t)tmp;
      pc++;

      void *fn = create_funptr(false, index);

      push_ptr(S, fn);
      pc++;
      break;
    }

    case ADDROF_NATIVE: {
      pc++;
      uint16_t tmp = (uint16_t)(P[pc]) << 8;
      pc++;
      tmp |= (uint16_t)P[pc];
      int16_t index = (int16_t)tmp;
      pc++;

      void *fn = create_funptr(true, index);

      push_ptr(S, fn);
      pc++;
      break;
    }

    case INVOKEDYNAMIC: {
      frame *F = xmalloc(sizeof(frame));
      F->S = S;
      F->P = P;
      F->pc = pc;
      F->V = V;
      push(callStack, (void*)F);

      void *f = pop_ptr(S);
      int16_t index = (int16_t)funptr2index(f);
      if (is_native_funptr(f)) {
        struct native_info *fn = &bc0->native_pool[index];
        int num_args = (int)fn->num_args;
        
        c0_value *A = xcalloc(sizeof(c0_value), num_args);
        for (int i = num_args - 1; i >= 0; i--) {
          A[i] = c0v_pop(S);
        }

        uint16_t f_index = fn->function_table_index;
        c0_value res = (*(native_function_table[f_index]))(A);
        c0v_push(S, res);
        pc++;
        break;
      } else {
        struct function_info *f = &bc0->function_pool[index];
        int num_vars = (int)f->num_vars;
        int num_args = (int)f->num_args;

        V = xcalloc(sizeof(c0_value), num_vars);
        for (int i = num_args - 1; i >= 0; i--) {
          V[i] = c0v_pop(S);
        }

        S = c0v_stack_new();
        P = f->code;
        pc = 0;
        break;
      }
    }

    default:
      fprintf(stderr, "invalid opcode: 0x%02x\n", P[pc]);
      abort();
    }
  }

  /* cannot get here from infinite loop */
  assert(false);
}