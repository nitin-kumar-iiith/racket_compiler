#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require data/queue)
(require "priority_queue.rkt")
(require "multigraph.rkt")
(require "interp.rkt")
(require "interp-Lvec.rkt")
(require "interp-Lvec-prime.rkt")
(require "type-check-Lvec.rkt")
(require "interp-Cvec.rkt")
(require "type-check-Cvec.rkt")
(require "interp-Lfun.rkt")
(require "interp-Lfun-prime.rkt")
(require "type-check-Lfun.rkt")
(require "utilities.rkt")
(require graph)
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]))

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; output of type-checking transitions from (Program ...) to (ProgramDefsExp ...) by type-check-Lfun
(define (shrink p)
  (match p
    [(ProgramDefsExp info defs body)
     (define (shrink-exp e)
       (match e
         [(Prim 'and `(,e1 ,e2))
          (If (shrink-exp e1) (shrink-exp e2) (Bool #f))]
         [(Prim 'or `(,e1 ,e2))
          (If (shrink-exp e1) (Bool #t) (shrink-exp e2))]
         [(Let var e1 e2)
          (Let var (shrink-exp e1) (shrink-exp e2))]
         [(SetBang var e)
          (SetBang var (shrink-exp e))]
         [(Begin es e)
          (Begin (map shrink-exp es) (shrink-exp e))]
         [(WhileLoop e1 e2)
          (WhileLoop (shrink-exp e1) (shrink-exp e2))]
         [(If e1 e2 e3)
          (If (shrink-exp e1) (shrink-exp e2) (shrink-exp e3))]
         [(Prim 'vector-ref `(,e1 ,e2))
          (Prim 'vector-ref `(,(shrink-exp e1) ,(shrink-exp e2)))]
         [(Prim 'vector-set! `(,e1 ,int ,e2))
          (Prim 'vector-set! `(,(shrink-exp e1) ,int ,(shrink-exp e2)))]
         [(HasType e type)
          (HasType (shrink-exp e) type)]
         [(Prim op es)
          (Prim op (map shrink-exp es))]
         [(Apply e es)
          (Apply (shrink-exp e)
                 (map shrink-exp es))]
         [(Def var p:t* rty info body)
          (Def var p:t* rty info (shrink-exp body))]
         [else e]))
     (define mainDef (Def 'main '() 'Integer '() body))
     (define defs^ (map shrink-exp (append defs `(,mainDef))))
     (define funame-arity
       (for/list ([d defs^])
         (cons (Def-name d) (length (Def-param* d)))))
     (ProgramDefs (cons (cons 'funame-arity funame-arity) info) defs^)]))

;; uniquify : R1 -> R1
(define (uniquify p)
  (define (uniquify-exp env)
    (lambda (e)
      (match e
        [(Var x) (Var (dict-ref env x))]
        [(Int n) (Int n)]
        [(Void) (Void)]
        [(Bool bool) (Bool bool)]
        [(SetBang var e)
         (define f (uniquify-exp env))
         (SetBang (dict-ref env var) (f e))]
        [(Let x e body)
         (let ([uniquified_x (gensym x)])
           (Let uniquified_x
                ((uniquify-exp env) e)
                ((uniquify-exp (dict-set env x uniquified_x)) body)))]
        [(WhileLoop e1 e2)
         (define f (uniquify-exp env))
         (WhileLoop (f e1) (f e2))]
        [(If e1 e2 e3)
         (define f (uniquify-exp env))
         (If (f e1) (f e2) (f e3))]
        [(Begin es e)
         (define f (uniquify-exp env))
         (Begin (map f es) (f e))]
        [(Prim 'vector-ref `(,e1 ,e2))
         (define f (uniquify-exp env))
         (Prim 'vector-ref `(,(f e1) ,(f e2)))]
        [(Prim 'vector-set! `(,e1 ,int ,e2))
         (define f (uniquify-exp env))
         (Prim 'vector-set! `(,(f e1) ,int ,(f e2)))]
        [(HasType e^ type)
         (define f (uniquify-exp env))
         (HasType (f e^) type)]
        [(Prim op es)
         (Prim op (for/list ([e es]) ((uniquify-exp env) e)))]
        [(Apply e es)
         (define f (uniquify-exp env))
         (Apply (f e) (map f es))]
        [(Def var (and p:t* (list `[,xs : ,ts] ...)) rty info body)
         (let ([new_env (append (map cons xs xs) env)])
           (Def var p:t* rty info ((uniquify-exp new_env) body)))])))
  (match p
    [(ProgramDefs info defs)
     (define funames (map car (dict-ref info 'funame-arity)))
     (define f (uniquify-exp (map cons funames funames)))
     (ProgramDefs info (map f defs))]))

(define (reveal_functions p)
  (match p
    [(ProgramDefs info defs)
     (define funame-arity (dict-ref info 'funame-arity))
     (define (reveal_exp e)
       (match e
         [(Var x) (let ([n (dict-ref funame-arity x #f)])
                    (if n (FunRef x) e))]
         [(Int n) (Int n)]
         [(Void) (Void)]
         [(Bool bool) (Bool bool)]
         [(SetBang var e)
          (SetBang var (reveal_exp e))]
         [(Let x e body)
          (Let x (reveal_exp e) (reveal_exp body))]
         [(WhileLoop e1 e2)
          (WhileLoop (reveal_exp e1) (reveal_exp e2))]
         [(If e1 e2 e3)
          (If (reveal_exp e1) (reveal_exp e2) (reveal_exp e3))]
         [(Begin es e)
          (Begin (map reveal_exp es) (reveal_exp e))]
         [(Prim 'vector-ref `(,e1 ,e2))
          (Prim 'vector-ref `(,(reveal_exp e1) ,(reveal_exp e2)))]
         [(Prim 'vector-set! `(,e1 ,int ,e2))
          (Prim 'vector-set! `(,(reveal_exp e1) ,int ,(reveal_exp e2)))]
         [(HasType e type)
          (HasType (reveal_exp e) type)]
         [(Prim op es)
          (Prim op (for/list ([e es]) (reveal_exp e)))]
         [(Apply e es)
          (Apply (reveal_exp e) (map reveal_exp es))]
         [(Def var (and p:t* (list `[,xs : ,ts] ...)) rty info body)
          (Def var p:t* rty info (reveal_exp body))]))
     (ProgramDefs info (map reveal_exp defs))]))

(define (limit_functions p)
  (match p
    [(ProgramDefs info defs)
     (define (limit_func_definition def)
       (match def
         [(Def var (and p:t* (list `[,xs : ,ts] ...)) rty info body)
          (cond [(> (length p:t*) 6)
                 (define xs_tail (list-tail xs 5))
                 (define ts_tail (list-tail ts 5))
                 (define para_acc_alters
                   (for/list ([k (in-naturals 0)]
                              [x xs_tail])
                     (cons (Var x) (Prim 'vector-ref (list (Var 'tup) (Int k))))))
                 (define p:t*^
                   (append (take p:t* 5) `([tup : (Vector ,@ts_tail)])))
                 (define body^
                   (let f ([e body])
                     (match e
                       [(Var x) (dict-ref para_acc_alters (Var x) (Var x))]
                       [(Let var rhs body)
                        (Let var (f rhs) (f body))]
                       [(If cnd thn els)
                        (If (f cnd) (f thn) (f els))]
                       [(SetBang var e)
                        (SetBang var (f e))]
                       [(Begin es e)
                        (Begin (map f es) (f e))]
                       [(WhileLoop cnd body)
                        (WhileLoop (f cnd) (f body))]
                       [(Prim 'vector-ref `(,e1 ,e2))
                        (Prim 'vector-ref `(,(f e1) ,(f e2)))]
                       [(Prim 'vector-set! `(,e1 ,int ,e2))
                        (Prim 'vector-set! `(,(f e1) ,int ,(f e2)))]
                       [(Prim op es) (Prim op (map f es))]
                       [(HasType (Prim 'vector es) type)
                        (HasType (Prim 'vector (map f es)) type)]
                       [(Apply e es)
                        (cond [(> (length es) 6)
                               (define-values (head tail) (split-at (map f es) 5))
                               (Apply (f e) (append head `(,(Prim 'vector `(,@tail)))))]
                              [else (Apply (f e) (map f es))])]
                       [else e])))
                 (Def var p:t*^ rty info body^)]
                [else (Def var p:t* rty info body)])]))
     (define (limit_func_application def)
       (match def
         [(Def var (and p:t* (list `[,xs : ,ts] ...)) rty info body)
          (define body^
            (let f ([e body])
              (match e
                [(Let var rhs body)
                 (Let var (f rhs) (f body))]
                [(If cnd thn els)
                 (If (f cnd) (f thn) (f els))]
                [(SetBang var e)
                 (SetBang var (f e))]
                [(Begin es e)
                 (Begin (map f es) (f e))]
                [(WhileLoop cnd body)
                 (WhileLoop (f cnd) (f body))]
                [(Prim 'vector-ref `(,e1 ,e2))
                 (Prim 'vector-ref `(,(f e1) ,(f e2)))]
                [(Prim 'vector-set! `(,e1 ,int ,e2))
                 (Prim 'vector-set! `(,(f e1) ,int ,(f e2)))]
                [(Prim op es) (Prim op (map f es))]
                [(HasType (Prim 'vector es) type)
                 (HasType (Prim 'vector (map f es)) type)]
                [(Apply e es)
                 (cond [(> (length es) 6)
                        (define-values (head tail) (split-at (map f es) 5))
                        (Apply (f e) (append head `(,(Prim 'vector `(,@tail)))))]
                       [else (Apply (f e) (map f es))])]
                [else e])))
          (Def var p:t* rty info body^)]))
     (ProgramDefs info (map (lambda (def)
                              (limit_func_application
                               (limit_func_definition def)))
                            defs))]))

(define (expose_allocation p)
  (match p
    [(Program info e)
     (define (expo_alloc_handler e)
       (match e
         [(Int int) e]
         [(Var var) e]
         [(Bool bool) e]
         [(Void) e]
         [(Let var rhs body)
          (Let var (expo_alloc_handler rhs)
               (expo_alloc_handler body))]
         [(If cnd thn els)
          (If (expo_alloc_handler cnd)
              (expo_alloc_handler thn)
              (expo_alloc_handler els))]
         [(GetBang var) e]
         [(SetBang var e^)
          (SetBang var (expo_alloc_handler e^))]
         [(Begin es e^)
          (Begin (map expo_alloc_handler es)
                 (expo_alloc_handler e^))]
         [(WhileLoop cnd body)
          (WhileLoop (expo_alloc_handler cnd)
                     (expo_alloc_handler body))]
         [(Prim 'vector-ref `(,e1 ,e2))
          (Prim 'vector-ref
                `(,(expo_alloc_handler e1)
                  ,(expo_alloc_handler e2)))]
         [(Prim 'vector-set! `(,e1 ,int ,e2))
          (Prim 'vector-set!
                `(,(expo_alloc_handler e1)
                  ,int
                  ,(expo_alloc_handler e2)))]
         [(Prim op es)
          (Prim op (map expo_alloc_handler es))]
         [(HasType (Prim 'vector es) type)
          (let* ([len (length es)]
                 [bytes (+ 8 (* len 8))]
                 [pos->var (for/list ([pos (in-range len)])
                             (cons pos (gensym 'vecinit)))]
                 [alloc (gensym 'alloc)]
                 [tupleinit
                  (foldr (lambda (pos-var accu)
                           (let ([pos (car pos-var)]
                                 [var (cdr pos-var)])
                             (Let (gensym '_)
                                  (Prim 'vector-set!
                                        `(,(Var alloc) ,(Int pos) ,(Var var)))
                                  accu)))
                         (Var alloc)
                         pos->var)]
                 [coll_alloc_tupleinit
                  (Let (gensym '_)
                       (If (Prim '< `(,(Prim '+ `(,(GlobalValue 'free_ptr) ,(Int bytes)))
                                      ,(GlobalValue 'fromspace_end)))
                           (Void)
                           (Collect bytes))
                       (Let alloc (Allocate len type) tupleinit))]
                 [bind_coll_alloc_tupleinit
                  (foldr (lambda (var-e accu)
                           (let ([var (car var-e)]
                                 [e (cdr var-e)])
                             (Let var (expo_alloc_handler e) accu)))
                         coll_alloc_tupleinit
                         (map (lambda (pos-var e)
                                (cons (cdr pos-var) e))
                              pos->var
                              es))])
            bind_coll_alloc_tupleinit)]))
     (Program info (expo_alloc_handler e))]))

(define (uncover-get! p)
  (match p
    [(ProgramDefs info defs)
     (define (collect-set! e)
       (match e
         [(Prim 'vector-ref `(,e1 ,e2))
          (set-union (collect-set! e1)
                     (collect-set! e2))]
         [(Prim 'vector-set! `(,e1 _ ,e2))
          (set-union (collect-set! e1)
                     (collect-set! e2))]
         [(Prim one-arg `(,e)) (collect-set! e)]
         [(Prim two-args `(,e1 ,e2))
          (set-union (collect-set! e1)
                     (collect-set! e2))]
         [(Let var rhs body)
          (set-union (collect-set! rhs)
                     (collect-set! body))]
         [(If cnd thn els)
          (set-union (collect-set! cnd)
                     (collect-set! thn)
                     (collect-set! els))]
         [(SetBang var e) (set var)]
         [(Begin es e)
          (foldl
           (lambda (e accu) (set-union (collect-set! e) accu))
           (set)
           (cons e es))]
         [(WhileLoop e1 e2)
          (set-union (collect-set! e1)
                     (collect-set! e2))]
         [(Apply e es)
          (foldl (lambda (e accu) (set-union (collect-set! e) accu))
                 (set)
                 (cons e es))]
         [else (set)]))
     (define ((uncover-get!-exp set!-vars) e)
       (define f (uncover-get!-exp set!-vars))
       (match e
         [(Var x) (if (set-member? set!-vars x)
                      (GetBang x)
                      (Var x))]
         [(Prim 'vector-ref `(,e1 ,e2))
          (Prim 'vector-ref `(,(f e1) ,(f e2)))]
         [(Prim 'vector-set! `(,e1 ,int ,e2))
          (Prim 'vector-set! `(,(f e1) ,int ,(f e2)))]
         [(Prim one-arg `(,e))
          (Prim one-arg `(,(f e)))]
         [(Prim two-args `(,e1 ,e2))
          (Prim two-args `(,(f e1) ,(f e2)))]
         [(Let var rhs body)
          (Let var (f rhs) (f body))]
         [(If cnd thn els)
          (If (f cnd) (f thn) (f els))]
         [(SetBang var e)
          (SetBang var (f e))]
         [(Begin es e) (Begin (map f es) (f e))]
         [(WhileLoop e1 e2) (WhileLoop (f e1) (f e2))]
         [(Apply e es) (Apply (f e) (map f es))]
         [else e]))
     (define defs^
       (for/list ([d defs])
         (match d
           [(Def var p:t* rty info body)
            (Def var p:t* rty info ((uncover-get!-exp (collect-set! body)) body))])))
     (ProgramDefs info defs^)]))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (letrec ([rco_atm
            (lambda (e)
              (match e
                [(Int int) (values e '())]
                [(Var var) (values e '())]
                [(Void) (values e '())]
                [(Bool bool) (values e '())]
                [(Prim 'read '())
                 (let ([tmp-name (gensym 'tmp)])
                   (values tmp-name
                     (cons (cons tmp-name e)
                       '())))]
                [(Collect int)
                 (let ([tmp-name (gensym 'tmp)])
                   (values tmp-name
                     (cons (cons tmp-name e)
                       '())))]
                [(Allocate int type)
                 (let ([tmp-name (gensym 'tmp)])
                   (values tmp-name
                     (cons (cons tmp-name e)
                       '())))]
                [(GlobalValue var)
                 (let ([tmp-name (gensym 'tmp)])
                   (values tmp-name
                     (cons (cons tmp-name e)
                       '())))]
                [(Prim one-arg `(,arg)) ;; Do I need to make sure that arg is atomic? - absolutely
                 (define-values (name env) (rco_atm arg))
                 (let ([tmp-name (gensym 'tmp)]
                       [v (dict-ref env name #f)])
                   (values tmp-name
                     (cons
                       (cons tmp-name
                         (if v (Let name v (Prim one-arg (list (Var name)))) e))
                       env)))]
                [(Prim two-args `(,arg1 ,arg2))
                 (define-values (name1 env1) (rco_atm arg1))
                 (define-values (name2 env2) (rco_atm arg2))
                 (let ([tmp-name (gensym 'tmp)]
                       [v1 (dict-ref env1 name1 #f)]
                       [v2 (dict-ref env2 name2 #f)])
                   (values tmp-name
                     (cons (cons tmp-name
                             (cond [(and v1 v2)
                                    (Let name1 v1
                                      (Let name2 v2
                                        (Prim two-args (list (Var name1) (Var name2)))))]
                                   [v1 (Let name1 v1
                                         (Prim two-args (list (Var name1) name2)))]
                                   [v2 (Let name2 v2
                                         (Prim two-args (list name1 (Var name2))))]
                                   [else e]))
                           (append env1 env2))))]
                [(Prim 'vector-set! `(,e1 ,int ,e2))
                 (define-values (name1 env1) (rco_atm e1))
                 (define-values (name2 env2) (rco_atm e2))
                 (let ([tmp-name (gensym 'tmp)]
                       [v1 (dict-ref env1 name1 #f)]
                       [v2 (dict-ref env2 name2 #f)])
                   (values tmp-name
                     (cons (cons tmp-name
                             (cond [(and v1 v2)
                                    (Let name1 v1
                                      (Let name2 v2
                                        (Prim 'vector-set! (list (Var name1) int (Var name2)))))]
                                   [v1 (Let name1 v1
                                         (Prim 'vector-set! (list (Var name1) int name2)))]
                                   [v2 (Let name2 v2
                                         (Prim 'vector-set! (list name1 int (Var name2))))]
                                   [else e]))
                           (append env1 env2))))]
                [(GetBang var)
                 (let ([tmp-name (gensym 'tmp)])
                   (values tmp-name
                           (cons (cons tmp-name (Var var))
                                 '())))]
                [(SetBang var e)
                 (let ([tmp-name (gensym 'tmp)])
                   (values tmp-name
                           (cons (cons tmp-name (SetBang var (rco_exp e)))
                                 '())))]
                [(Begin es e)
                 (let ([tmp-name (gensym 'tmp)])
                   (values tmp-name
                           (cons (cons tmp-name (Begin (map rco_exp es) (rco_exp e)))
                                 '())))]
                [(WhileLoop e1 e2)
                 (let ([tmp-name (gensym 'tmp)])
                   (values tmp-name
                           (cons (cons tmp-name (WhileLoop (rco_exp e1) (rco_exp e2)))
                                 '())))]
                [(Let var e1 e2)
                 (let ([tmp-name (gensym 'tmp)])
                   (values tmp-name
                     (cons
                       (cons tmp-name (Let var (rco_exp e1) (rco_exp e2)))
                       '())))]
                [(If e1 e2 e3)
                 (let ([tmp-name (gensym 'tmp)])
                   (values tmp-name
                     (cons
                       (cons tmp-name (If (rco_exp e1) (rco_exp e2) (rco_exp e3)))
                       '())))]))]
           [rco_exp
            (lambda (e)
              (match e
                [(Int int) e]
                [(Var var) e]
                [(Void) e]
                [(Bool bool) e]
                [(Prim 'read '()) e]
                [(Collect int) e]
                [(Allocate int type) e]
                [(GlobalValue var) e]
                [(Prim op es)
                 (define-values (name env) (rco_atm e)) ;; (- (- 10)) (let ((tmp (- 10))) (- tmp))
                 (dict-ref env name)]
                [(GetBang var)
                 (define-values (name env) (rco_atm e))
                 (dict-ref env name)]
                [(SetBang var e) (SetBang var (rco_exp e))]
                [(Begin es e) (Begin (map rco_exp es) (rco_exp e))]
                [(WhileLoop e1 e2) (WhileLoop (rco_exp e1) (rco_exp e2))]
                [(Let var e1 e2) (Let var (rco_exp e1) (rco_exp e2))]
                [(If e1 e2 e3) (If (rco_exp e1) (rco_exp e2) (rco_exp e3))]))])
    (match p
      [(Program info e) (Program info (rco_exp e))])))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (define blocks '())
  (letrec ([explicate_tail
            (lambda (promise)
              (define e (force promise))
              (match e
                [(Var x) (delay (Return (Var x)))]
                [(Bool b) (delay (Return (Bool b)))]
                [(Int n) (delay (Return (Int n)))]
                [(Void) (delay (Return (Void)))]
                [(Allocate int type)
                 (delay (Return (Allocate int type)))]
                [(GlobalValue var)
                 (delay (Return (GlobalValue var)))]
                [(Collect int)
                 (delay (Collect int) (Return (Void)))]
                [(Let x rhs body)
                 (explicate_assign
                  (delay (values (delay rhs)
                                 (delay x)
                                 (delay (explicate_tail (delay body))))))]
                [(If cnd thn els)
                 (explicate_pred
                  (delay (values (delay cnd)
                                 (delay (explicate_tail (delay thn)))
                                 (delay (explicate_tail (delay els))))))]
                [(Prim op atms) (delay (Return (Prim op atms)))]
                [(SetBang var e^)
                 (explicate_effect
                  (delay (values (delay e)
                                 (delay
                                   (explicate_tail (delay (Void)))))))]
                [(Begin es e^)
                 (force (foldr
                         (lambda (e accu)
                           (delay (explicate_effect
                                   (delay (values (delay e) accu)))))
                         (delay (explicate_tail (delay e^)))
                         es))]
                [(WhileLoop cnd body)
                 (explicate_effect
                  (delay (values (delay e)
                                 (delay
                                   (explicate_tail (delay (Void)))))))]
                [else (error "explicate_tail unhandled case" e)]))]
           [explicate_assign
            (lambda (promise)
              (define-values (e x cont) (force promise))
              (define e^ (force e))
              (match e^
                [(Var y) (delay (Seq (Assign (Var (force x)) (Var y))
                                     (force (force cont))))]
                [(Bool b) (delay (Seq (Assign (Var (force x)) (Bool b))
                                      (force (force cont))))]
                [(Int n) (delay (Seq (Assign (Var (force x)) (Int n))
                                     (force (force cont))))]
                [(Void) (delay (Seq (Assign (Var (force x)) (Void))
                                    (force (force cont))))]
                [(Allocate int type)
                 (delay (Seq (Assign (Var (force x))
                                     (Allocate int type))
                             (force (force cont))))]
                [(GlobalValue var)
                 (delay (Seq (Assign (Var (force x))
                                     (GlobalValue var))
                             (force (force cont))))]
                [(Collect int)
                 (delay (Seq (Collect int)
                             (force (force cont))))]
                [(Let y rhs body)
                 (explicate_assign
                  (delay (values (delay rhs)
                                 (delay y)
                                 (delay
                                   (explicate_assign
                                    (delay (values (delay body)
                                                   x
                                                   cont)))))))]
                [(If cnd thn els)
                 ;; create a new block to store the code of cont
                 ;; to avoid duplicate code when cnd is not a boolean value.
                 (let ([cont^ (create-block (force cont))])
                   (explicate_pred
                    (delay (values (delay cnd)
                                   (delay
                                     (explicate_assign
                                      (delay (values (delay thn) x cont^))))
                                   (delay
                                     (explicate_assign
                                      (delay (values (delay els) x cont^))))))))]
                [(Prim op es) (delay (Seq (Assign (Var (force x)) (Prim op es))
                                          (force (force cont))))]
                [(SetBang var e^^)
                 (explicate_effect
                  (delay (values (delay e^)
                                 (delay
                                   (explicate_assign
                                    (delay (values (delay (Void)) x cont)))))))]
                [(WhileLoop cnd body)
                 (explicate_effect
                  (delay (values (delay e^)
                                 (delay
                                   (explicate_assign
                                    (delay (values (delay (Void)) x cont)))))))]
                [(Begin es e^^) ;; the side effect of e^^ should
                 (force (foldr  ;; not be computed twice.
                         (lambda (e accu)
                           (delay
                             (explicate_effect
                              (delay (values (delay e) accu)))))
                         (delay (explicate_assign (delay (values (delay e^^) x cont))))
                         es))]
                [else (error "explicate_assign unhandled case" e)]))]
           [explicate_pred
            (lambda (promise)
              (define-values (cnd thn els) (force promise))
              (define cnd^ (force cnd))
              (match cnd^
                [(Var x)
                 (explicate_pred
                  (delay (values (delay (Prim 'eq? `(,(Var x) ,(Bool #t)))) thn els)))]
                [(Bool b)
                 (if b (force thn) (force els))]
                [(Let x rhs body)
                 (explicate_assign
                  (delay (values (delay rhs)
                                 (delay x)
                                 (delay
                                   (explicate_pred
                                    (delay (values (delay body) thn els)))))))]
                [(Prim 'not `(,e))
                 (explicate_pred
                  (delay (values (delay (Prim 'eq? `(,e ,(Bool #f)))) thn els)))]
                [(Prim op es)
                 (delay (IfStmt (Prim op es)
                                (force (create-block (force thn)))
                                (force (create-block (force els)))))]
                [(If cnd^ thn^ els^)
                 (explicate_pred
                  (delay (values (delay cnd^)
                                 (delay
                                   (explicate_pred
                                    (delay (values (delay thn^) thn els))))
                                 (delay
                                   (explicate_pred
                                    (delay (values (delay els^) thn els)))))))]
                [(Begin es e^)
                 (force (foldr
                         (lambda (e accu)
                           (delay
                             (explicate_effect
                              (delay (values (delay e) accu)))))
                         (delay (explicate_pred (delay (values (delay e^) thn els))))
                         es))]
                [(SetBang _ _)
                 (error 'explicate_control "expected a boolean value, got ~a" cnd^)]
                [(WhileLoop _ _)
                 (error 'explicate_control "expected a boolean value, got ~a" cnd^)]
                [(Allocate int type)
                 (error 'explicate_control "expected a boolean value, got ~a" cnd^)]
                [(GlobalValue var)
                 (error 'explicate_control "expected a boolean value, got ~a" cnd^)]
                [(Collect int)
                 (error 'explicate_control "expected a boolean value, got ~a" cnd^)]
                [else (error "explicate_pred unhandled case" cnd^)]))]
           [explicate_effect
            (lambda (promise)
              (define-values (e cont) (force promise))
              (define e^ (force e))
              (match e^
                ;; avoid duplicate computation of side effects
                [(SetBang var e)
                 (explicate_assign
                  (delay (values (delay e) (delay var) cont)))]
                [(Begin es e)
                 (force (foldr
                         (lambda (e accu)
                           (delay (explicate_effect
                                   (delay (values e accu)))))
                         (delay
                           (explicate_effect
                            (delay (values (delay e) cont))))
                         es))]
                [(WhileLoop cnd body)
                 (let* ([loop (gensym 'loop)]
                        [tail
                         (explicate_pred
                          (delay (values (delay cnd)
                                         (delay
                                           (explicate_effect
                                            (delay (values (delay body) (delay (Goto loop))))))
                                         cont)))])
                   (set! blocks (cons (cons loop (force tail)) blocks))
                   (delay (Goto loop)))]
                [(Let var e1 e2)
                 (explicate_assign
                  (delay (values (delay e1)
                                 (delay var)
                                 (delay
                                   (explicate_effect
                                    (delay (values (delay e2) cont)))))))]
                [(If e1 e2 e3)
                 ;; create a new block to store the code of cont
                 ;; to avoid duplicate code when e1 is not a boolean value.
                 (let ([cont^ (create-block (force cont))])
                   (explicate_pred
                    (delay (values (delay e1)
                                   (delay
                                     (explicate_effect
                                      (delay (values (delay e2) cont^))))
                                   (delay
                                     (explicate_effect
                                      (delay (values (delay e3) cont^))))))))]
                [(Prim 'vector-set! `(,tup ,(Int n) ,rhs))
                 (explicate_assign
                  (delay (values (delay e^) (delay (gensym '_)) cont)))]
                [(Collect int)
                 (explicate_assign
                  (delay (values (delay e^) (delay (gensym '_)) cont)))]
                [else (force cont)]))]
           [create-block
            (lambda (tail)
              (delay
                (define t (force tail))
                (match t
                  [(Goto label) (Goto label)]
                  [else
                   (let ([label (gensym 'block)])
                     (set! blocks (cons (cons label t) blocks))
                     (Goto label))])))])
    (match p
      [(Program info body)
       (let ([body^ (force (explicate_tail (delay body)))])
         (CProgram info (cons (cons 'start body^) blocks)))])))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (define var->value (make-hash))
  (letrec ([tail-handler
            (lambda (tail)
              (match tail
                [(Return e)
                 (append
                  (stmt-handler (Assign (Reg 'rax) e))
                  (list (Jmp 'conclusion)))]
                [(Seq stmt tail)
                 (append
                  (stmt-handler stmt)
                  (tail-handler tail))]
                [(Goto label) (list (Jmp label))]
                [(IfStmt (Prim 'eq? `(,atm1 ,atm2)) (Goto thnl) (Goto elsl))
                 (let ([atm1^ (atm-handler atm1)]
                       [atm2^ (atm-handler atm2)])
                   (list (Instr 'cmpq (list atm2^ atm1^))
                         (JmpIf 'e thnl)
                         (Jmp elsl)))]
                [(IfStmt (Prim '< `(,atm1 ,atm2)) (Goto thnl) (Goto elsl))
                 (let ([atm1^ (atm-handler atm1)]
                       [atm2^ (atm-handler atm2)])
                   (list (Instr 'cmpq (list atm2^ atm1^))
                         (JmpIf 'l thnl)
                         (Jmp elsl)))]
                [(IfStmt (Prim '<= `(,atm1 ,atm2)) (Goto thnl) (Goto elsl))
                 (let ([atm1^ (atm-handler atm1)]
                       [atm2^ (atm-handler atm2)])
                   (list (Instr 'cmpq (list atm2^ atm1^))
                         (JmpIf 'le thnl)
                         (Jmp elsl)))]
                [(IfStmt (Prim '> `(,atm1 ,atm2)) (Goto thnl) (Goto elsl))
                 (let ([atm1^ (atm-handler atm1)]
                       [atm2^ (atm-handler atm2)])
                   (list (Instr 'cmpq (list atm2^ atm1^))
                         (JmpIf 'g thnl)
                         (Jmp elsl)))]
                [(IfStmt (Prim '>= `(,atm1 ,atm2)) (Goto thnl) (Goto elsl))
                 (let ([atm1^ (atm-handler atm1)]
                       [atm2^ (atm-handler atm2)])
                   (list (Instr 'cmpq (list atm2^ atm1^))
                         (JmpIf 'ge thnl)
                         (Jmp elsl)))]))]
           [stmt-handler
            (lambda (stmt)
              (match stmt
                [(Assign v e)
                 (match e
                   [(Prim 'read '())
                    (dict-set! var->value v (Reg 'rax))
                    (list (Callq 'read_int 0)
                          (Instr 'movq (list (Reg 'rax) v)))]
                   [(Prim '- `(,atm))
                    (let* ([atm^ (atm-handler atm)]
                           [atm^-value (dict-ref var->value atm^ atm^)]
                           [v-value (dict-ref var->value v v)])
                      (dict-set! var->value v v)
                      (cond [(eq? atm^-value v-value)
                             (list (Instr 'negq (list v)))]
                            [else
                             (list (Instr 'movq (list atm^ v))
                                   (Instr 'negq (list v)))]))]
                   [(Prim 'not `(,atm))
                    (let* ([atm^ (atm-handler atm)]
                           [atm^-value (dict-ref var->value atm^ atm^)]
                           [v-value (dict-ref var->value v v)])
                      (dict-set! var->value v v)
                      (cond [(eq? atm^-value v-value)
                             (list (Instr 'xorq (list (Imm 1) v)))]
                            [else
                             (list (Instr 'movq (list atm^ v))
                                   (Instr 'xorq (list (Imm 1) v)))]))]
                   [(Prim '+ `(,atm1 ,atm2))
                    (let* ([atm1^ (atm-handler atm1)]
                           [atm2^ (atm-handler atm2)]
                           [v-value (dict-ref var->value v v)]
                           [atm1^-value (dict-ref var->value atm1^ atm1^)]
                           [atm2^-value (dict-ref var->value atm2^ atm2^)])
                      (dict-set! var->value v v)
                      (cond
                        [(equal? atm1^-value v-value)
                         (list (Instr 'addq (list atm2^ v)))]
                        [(equal? atm2^-value v-value)
                         (list (Instr 'addq (list atm1^ v)))]
                        [else
                         (list (Instr 'movq (list atm1^ v))
                               (Instr 'addq (list atm2^ v)))]))]
                   [(Prim '- `(,atm1 ,atm2))
                    (let ([atm1^ (atm-handler atm1)]
                          [atm2^ (atm-handler atm2)])
                      (cond
                        [(equal? atm1^ v)
                         (list (Instr 'subq (list atm2^ v)))]
                        [else
                         (list (Instr 'movq (list atm1^ v))
                               (Instr 'subq (list atm2^ v)))]))]
                   [(Prim 'eq? `(,atm1 ,atm2))
                    (let ([atm1^ (atm-handler atm1)]
                          [atm2^ (atm-handler atm2)])
                      (list (Instr 'cmpq (list atm2^ atm1^))
                            (Instr 'set (list 'e (ByteReg 'al)))
                            (Instr 'movzbq (list (ByteReg 'al) v))))]
                   [(Prim '< `(,atm1 ,atm2))
                    (let ([atm1^ (atm-handler atm1)]
                          [atm2^ (atm-handler atm2)])
                      (list (Instr 'cmpq (list atm2^ atm1^))
                            (Instr 'set (list 'l (ByteReg 'al)))
                            (Instr 'movzbq (list (ByteReg 'al) v))))]
                   [(Prim '<= `(,atm1 ,atm2))
                    (let ([atm1^ (atm-handler atm1)]
                          [atm2^ (atm-handler atm2)])
                      (list (Instr 'cmpq (list atm2^ atm1^))
                            (Instr 'set (list 'le (ByteReg 'al)))
                            (Instr 'movzbq (list (ByteReg 'al) v))))]
                   [(Prim '> `(,atm1 ,atm2))
                    (let ([atm1^ (atm-handler atm1)]
                          [atm2^ (atm-handler atm2)])
                      (list (Instr 'cmpq (list atm2^ atm1^))
                            (Instr 'set (list 'g (ByteReg 'al)))
                            (Instr 'movzbq (list (ByteReg 'al) v))))]
                   [(Prim '>= `(,atm1 ,atm2))
                    (let ([atm1^ (atm-handler atm1)]
                          [atm2^ (atm-handler atm2)])
                      (list (Instr 'cmpq (list atm2^ atm1^))
                            (Instr 'set (list 'ge (ByteReg 'al)))
                            (Instr 'movzbq (list (ByteReg 'al) v))))]
                   [(Prim 'vector-ref `(,tup ,(Int n)))
                    (let ([tup^ (atm-handler tup)])
                      (list (Instr 'movq (list tup^ (Reg 'r11)))
                            (Instr 'movq (list (Deref 'r11 (* 8 (+ n 1))) v))))]
                   [(Prim 'vector-set! `(,tup ,(Int n) ,rhs))
                    (let ([tup^ (atm-handler tup)]
                          [rhs^ (atm-handler rhs)])
                      (list (Instr 'movq (list tup^ (Reg 'r11)))
                            (Instr 'movq (list rhs^ (Deref 'r11 (* 8 (+ n 1)))))
                            (Instr 'movq (list (Imm 0) v))))]
                   [(Prim 'vector-length `(,tup))
                    (let ([tup^ (atm-handler tup)])
                      (list (Instr 'movq (list tup^ (Reg 'r11)))
                            (Instr 'movq (list (Deref 'r11 0) (Reg 'rax)))
                            (Instr 'sarq (list (Reg 'rax) (Imm 1)))
                            (Instr 'andq (list (Reg 'rax) (Imm 63)))
                            (Instr 'movq (list (Reg 'rax) v))))]
                   [(Allocate len type)
                    (define pointer_mask
                      (match type
                        [`(Vector ,ts ...)
                         (let f ([power 1] [ts ts])
                           (match ts
                             [`((Vector ,_ ...) ,ts^ ...) (+ power (f (* power 2) ts^))]
                             [`(,_ ,ts^ ...) (f (* power 2) ts^)]
                             ['() 0]))]
                        [else (error 'select-instructions "expect Vector, got ~v\n" type)]))
                    (define tuple_tag (+ (* (+ (* pointer_mask 64) len) 2) 1))
                    (list (Instr 'movq (list (Global 'free_ptr) (Reg 'r11)))
                          (Instr 'addq (list (Imm (* 8 (+ len 1))) (Global 'free_ptr)))
                          (Instr 'movq (list (Imm tuple_tag) (Deref 'r11 0)))
                          (Instr 'movq (list (Reg 'r11) v)))]
                   [(Int int) (list (Instr 'movq (list (atm-handler e) v)))]
                   [(Var var) (list (Instr 'movq (list (atm-handler e) v)))]
                   [(Bool bool) (list (Instr 'movq (list (atm-handler e) v)))]
                   [(Void) (list (Instr 'movq (list (atm-handler e) v)))]
                   [(GlobalValue var) (list (Instr 'movq (list (atm-handler e) v)))])]
                [(Prim 'read '()) (list (Callq 'read_int 0))]
                [(Prim 'vector-set! `(,tup ,(Int n) ,rhs))
                 (let ([tup^ (atm-handler tup)]
                       [rhs^ (atm-handler rhs)])
                   (list (Instr 'movq (list tup^ (Reg 'r11)))
                         (Instr 'movq (list rhs^ (Deref 'r11 (* 8 (+ n 1)))))))]
                [(Collect bytes)
                 (list (Instr 'movq (list (Reg 'r15) (Reg 'rdi)))
                       (Instr 'movq (list (Imm bytes) (Reg 'rsi)))
                       (Callq 'collect 2))]))]
           [atm-handler
            (lambda (atm)
              (match atm
                [(Int int) (Imm int)]
                [(Bool bool) (if bool (Imm 1) (Imm 0))]
                [(Var var) atm]
                [(Void) (Imm 0)]
                [(GlobalValue label) (Global label)]))])
    (match p
      [(CProgram info latas)
       (let ([latas^
              (for/list ([label-tail latas])
                (let ([label (car label-tail)]
                      [tail (cdr label-tail)])
                  (cons label (Block '() (tail-handler tail)))))])
         (X86Program info latas^))])))

(define (W instr)
  (match instr
    [(Instr 'addq `(,arg1 ,arg2)) (CLL arg2)]
    [(Instr 'subq `(,arg1 ,arg2)) (CLL arg2)]
    [(Instr 'negq `(,arg)) (CLL arg)]
    [(Instr 'movq `(,arg1 ,arg2)) (CLL arg2)]
    [(Instr 'popq `(,arg)) (CLL arg)]
    [(Callq label int)
     (set
      (Reg 'rax) (Reg 'rcx) (Reg 'rdx) (Reg 'rsi)
      (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10) (Reg 'r11))]
    [(Instr 'xorq `(,arg1 ,arg2)) (CLL arg2)]
    [(Instr 'set `(,cc ,arg)) (CLL arg)]
    [(Instr 'movzbq `(,arg1 ,arg2)) (CLL arg2)]
    [(Instr 'andq `(,arg1 ,arg2)) (CLL arg1)]
    [(Instr 'sarq `(,arg1 ,arg2)) (CLL arg1)]
    [else (set)]))

(define (R instr)
  (match instr
    [(Instr 'addq `(,arg1 ,arg2))
     (set-union (CLL arg1) (CLL arg2))]
    [(Instr 'subq `(,arg1 ,arg2))
     (set-union (CLL arg1) (CLL arg2))]
    [(Instr 'negq `(,arg)) (CLL arg)]
    [(Instr 'movq `(,arg1 ,arg2)) (CLL arg1)]
    [(Instr 'pushq `(,arg)) (CLL arg)]
    [(Callq label int)
     (list->set
      (take
       (list (Reg 'rdi) (Reg 'rsi) (Reg 'rdx)
             (Reg 'rcx) (Reg 'r8) (Reg 'r9))
       int))]
    [(Instr 'xorq `(,arg1 ,arg2))
     (set-union (CLL arg1) (CLL arg2))]
    [(Instr 'cmpq `(,arg1 ,arg2))
     (set-union (CLL arg1) (CLL arg2))]
    [(Instr 'movzbq `(,arg1 ,arg2)) (CLL arg1)]
    [(Instr 'andq `(,arg1 ,arg2))
     (set-union (CLL arg1) (CLL arg2))]
    [(Instr 'sarq `(,arg1 ,arg2))
     (set-union (CLL arg1) (CLL arg2))]
    [else (set)]))

(define (CLL arg)
  (match arg
    [(Imm int) (set)]
    [else (set arg)]))

(define (uncover_live p)
  (match p
    [(X86Program info labs)
     (define (analyze_dataflow G transfer bottom join)
       (define mapping (make-hash))
       (for ([v (in-vertices G)])
         (dict-set! mapping v bottom))
       (dict-set! mapping 'conclusion (set (Reg 'rax) (Reg 'rsp)))
       (define worklist (make-queue))
       (for ([v (in-vertices G)]
             #:when (not (eq? v 'conclusion)))
         (enqueue! worklist v))
       (define trans-G (transpose G))
       (while (not (queue-empty? worklist))
         (define node (dequeue! worklist))
         (define input (for/fold ([state bottom])
                                 ([pred (in-neighbors G node)])
                         (join state (dict-ref mapping pred))))
         (define output (transfer node input))
         (cond [(not (set=? output (dict-ref mapping node)))
                (dict-set! mapping node output)
                (for ([v (in-neighbors trans-G node)])
                  (enqueue! worklist v))]))
       mapping)
     (define (transfer node input)
       (match (dict-ref labs node)
         [(Block info instructions)
          (foldr
           (lambda (instr accu)
             (match instr
               [(Jmp label) accu]
               [(JmpIf cc label) accu]
               [else
                (set-union
                 (set-subtract accu (W instr))
                 (R instr))]))
           input
           instructions)]))
     (define (join state pstate) (set-union state pstate))
     (define edges
       (foldl
        (lambda (lab accu)
          (match lab
            [(cons label_from (Block '() instrs))
             (let ([edges-of-block
                    (foldl
                     (lambda (instr accu)
                       (match instr
                         [(Jmp label_to)
                          ;; #:when (not (eq? label_to 'conclusion))
                          (cons (list label_from label_to) accu)]
                         [(JmpIf cc label_to)
                          (cons (list label_from label_to) accu)]
                         [else accu]))
                     '()
                     instrs)])
               (append edges-of-block accu))]))
        '()
        labs))
     (define graph (make-multigraph edges))
     (let ([label->live (analyze_dataflow graph transfer (set) join)])
       (define labs^
         (for/list ([lab labs])
           (match lab
             [(cons label (Block binfo instructions))
              (let* ([live-after-sets+
                     (foldr
                      (lambda (instr accu)
                        (match instr
                          [(Jmp label)
                           (cons (set-union (dict-ref label->live label)
                                            (car accu))
                                 accu)]
                          [(JmpIf cc label)
                           (cons (set-union (dict-ref label->live label)
                                            (car accu))
                                 accu)]
                          [else
                           (let* ([live-before-set-preinstr (car accu)]
                                  [live-after-set
                                   (set-union
                                    (set-subtract live-before-set-preinstr (W instr))
                                    (R instr))])
                             (cons live-after-set accu))]))
                      `(,(set))
                      instructions)]
                     [binfo^ (cons (cons 'live-after-sets (cdr live-after-sets+)) binfo)])
                (when (not (set=? (car live-after-sets+) (dict-ref label->live label)))
                  (error "unexpected live-before-set of block ~a, ~v != ~v\n"
                         label
                         (reverse live-after-sets+)))
                (cons label (Block binfo^ instructions)))])))
       (X86Program (cons (cons 'label->live label->live) info) labs^))]))

(define build_interference
  (lambda (p)
    (match p
      [(X86Program info labs)
       (let* ([caller-saved-regs
               (list (Reg 'rax) (Reg 'rcx) (Reg 'rdx)
                     (Reg 'rsi) (Reg 'rdi) (Reg 'r8)
                     (Reg 'r9) (Reg 'r10) (Reg 'r11))]
              [callee-saved-regs
               (list (Reg 'rsp) (Reg 'rbp) (Reg 'rbx)
                     (Reg 'r12) (Reg 'r13) (Reg 'r14) (Reg 'r15))]
              [v->type (dict-ref info 'locals-types)]
              [conflict-graph
              (letrec ([compute-graph
                        (lambda (instrs liafsets graph)
                          (if (null? instrs)
                              graph
                              (let ([instr (car instrs)]
                                    [liafset (car liafsets)])
                                (match instr
                                  [(Instr 'movq `(,arg1 ,arg2))
                                   (for ([v liafset])
                                     (when (and (not (equal? v arg1))
                                                (not (equal? v arg2)))
                                       (add-edge! graph v arg2)))]
                                  [(Instr 'movzbq `(,arg1 ,arg2))
                                   (for ([v liafset])
                                     (when (and (not (equal? v arg1))
                                                (not (equal? v arg2)))
                                       (add-edge! graph v arg2)))]
                                  [(Callq label int)
                                   (for ([v liafset])
                                     (for ([reg caller-saved-regs])
                                       (add-edge! graph v reg)))
                                   (when (eq? label 'collect)
                                     (for ([v liafset])
                                       (match (dict-ref v->type v 'not_vector)
                                         [`(Vector ,_ ...)
                                          (for ([reg callee-saved-regs])
                                            (add-edge! graph v reg))]
                                         [else (void)])))]
                                  [else
                                   (for* ([v liafset]
                                          [d (set->list (W instr))])
                                     (when (not (equal? v d))
                                       (add-edge! graph v d)))])
                                (compute-graph (cdr instrs) (cdr liafsets) graph))))])
                (foldl
                 (lambda (lab accu)
                   (match lab
                     [(cons label (Block binfo instructions))
                      (let ([liafsets (dict-ref binfo 'live-after-sets)])
                        (compute-graph instructions liafsets accu))]))
                 (undirected-graph '())
                 labs))])
         (X86Program (cons (cons 'conflicts conflict-graph) info) labs))])))

;; TODO: implement move biasing in challenge part of chap3
(define (allocate_registers p)
  ;; uncover_live : X86Var -> X86Var + live-after sets
    (match p
      [(X86Program info labs)
       (define avaliable_registers
         (list (cons 0 (Reg 'rcx)) (cons 1 (Reg 'rbx))
               (cons 2 (Reg 'r8)) (cons 3 (Reg 'r12))))
       (define (graph_coloring graph)
         (define v->color (list (cons (Reg 'rax) -1) (cons (Reg 'rsp) -2)
                                (cons (Reg 'r11) -3) (cons (Reg 'r15) -4)))
         ;; Faster?
         (define v->saturation
           (for/list ([v (in-vertices graph)]
                      #:when (Var? v)) ;; compute only the saturations of vars in graph
             (let ([saturation
                    (foldl (lambda (vertice accu)
                             (let ([color
                                    (dict-ref v->color vertice #f)])
                               (if color (cons color accu) accu)))
                           '()
                           (sequence->list (in-neighbors graph v)))])
               (cons v (list->set saturation)))))
         (define saturation-pq
           (make-pqueue
            (lambda (v1 v2)
              (>= (set-count (dict-ref v->saturation v1))
                  (set-count (dict-ref v->saturation v2))))))
         (define v->pq_handle
           (for/list ([v (in-vertices graph)]
                      #:when (Var? v)) ;; handle only the vars in graph
             (cons v (pqueue-push! saturation-pq v))))
         ;; (list (cons 0 (Reg 'rcx)) (cons 1 (Reg 'rdx))
         ;;       (cons 2 (Reg 'rsi)) (cons 3 (Reg 'rdi))
         ;;       (cons 4 (Reg 'r8)) (cons 5 (Reg 'r9))
         ;;       (cons 6 (Reg 'r10)) (cons 7 (Reg 'r11)))])
           (while (> (pqueue-count saturation-pq) 0)
             (let* ([v (pqueue-pop! saturation-pq)]
                    [s (dict-ref v->saturation v)]
                    [vs (sequence->list (in-neighbors graph v))])
               (for/first ([i (in-naturals 0)]
                           #:when (and (not (set-member? s i))
                                       (not (member (dict-ref avaliable_registers i #f) vs))))
                 (set! v->color (dict-set v->color v i)))
               (for ([adjv (in-neighbors graph v)]
                     #:when (Var? adjv))
                 (let* ([adjv-saturation
                         (dict-ref v->saturation adjv)]
                        [saturation^
                         (set-union adjv-saturation (set (dict-ref v->color v)))])
                   (set! v->saturation
                         (dict-set v->saturation adjv saturation^))))))
         (filter (lambda (v_color) (>= (cdr v_color) 0)) v->color))
       (define (compute_location v->color v->type)
         ;; return 1. v->location
         ;;        2. used-callee
         ;;        3. num-procedure-spills
         ;;        4. num-root-spills
         (define v->location (make-hash))
         (define color->register (make-hash))
         (define color->procedure_stack (make-hash))
         (define color->root_stack (make-hash))
         (define used-callee (mutable-set))
         (define num-procedure-spills 0)
         (define num-root-spills 0)
         (for ([var_color v->color])
           (let* ([var (car var_color)]
                  [color (cdr var_color)])
               (if (>= color (length avaliable_registers))
                   ;; spill
                   (match (dict-ref v->type (Var-name var))
                     [`(Vector ,_ ...)
                     ;; spill on root stack
                      (let ([location (dict-ref color->root_stack color #f)])
                        (unless location
                          (let ([offset (* num-root-spills 8)]) ;; grow upward, but how? - Yifan
                            (set! num-root-spills (+ num-root-spills 1))
                            (dict-set! color->root_stack color (Deref 'r15 offset))))
                        (dict-set! v->location var (dict-ref color->root_stack color)))]
                     [else
                     ;; spill on procedure call stack
                      (let ([location (dict-ref color->procedure_stack color #f)])
                        (unless location
                          (let ([offset (- (+ 8 (* (set-count used-callee) 8) (* num-procedure-spills 8)))]) ;; grow downward
                            (set! num-procedure-spills (+ num-procedure-spills 1))
                            (dict-set! color->procedure_stack color (Deref 'rbp offset))))
                        (dict-set! v->location var (dict-ref color->procedure_stack color)))])
                   ;; in registers
                   (let ([location (dict-ref color->register color #f)])
                     (unless location
                       (let ([register (dict-ref avaliable_registers color)])
                         (when (set-member? (set (Reg 'rsp) (Reg 'rbp) (Reg 'rbx)
                                                 (Reg 'r12) (Reg 'r13) (Reg 'r14) (Reg 'r15))
                                            register)
                           (set-add! used-callee register))
                         (dict-set! color->register color register)))
                     (dict-set! v->location var (dict-ref color->register color))))))
         (values v->location used-callee num-procedure-spills num-root-spills))
       (define v->color (graph_coloring (dict-ref info 'conflicts)))
       (define v->type (dict-ref info 'locals-types))
       (define-values
         (v->location used-callee num-procedure-spills num-root-spills)
         (compute_location v->color v->type))
       (define labels_blocks
         (for/list ([label_block labs])
           (match label_block
             [`(,label . ,(Block binfo instructions))
              (define instructions^
                (for/list ([instr instructions])
                  (match instr
                    [(Instr one-arg `(,arg))
                     (let ([arg^ (dict-ref v->location arg arg)])
                       (Instr one-arg `(,arg^)))]
                    [(Instr two-args `(,arg1 ,arg2))
                     (let ([arg1^ (dict-ref v->location arg1 arg1)]
                           [arg2^ (dict-ref v->location arg2 arg2)])
                       (Instr two-args `(,arg1^ ,arg2^)))]
                    [else instr])))
              `(,label . ,(Block binfo instructions^))])))
       (X86Program (append `(,(cons 'used-callee used-callee)
                             ,(cons 'v->location v->location)
                             ,(cons 'v->color v->color)
                             ,(cons 'num-procedure-spills num-procedure-spills)
                             ,(cons 'num-root-spills num-root-spills))
                           info)
                   labels_blocks)]))

(define (remove_jumps p)
  (match p
    [(X86Program info labs)
     (define node->instrs (make-hash))
     (for ([node labs])
       (dict-set! node->instrs (car node) (Block-instr* (cdr node))))
     (define node->n-preblock (make-hash))
     (for ([node labs])
       (for ([instr (Block-instr* (cdr node))])
         (match instr
           [(Jmp label)
            (dict-set! node->n-preblock
                       label
                       (+ (dict-ref! node->n-preblock label 0) 1))]
           [(JmpIf cc label)
            (dict-set! node->n-preblock
                       label
                       (+ (dict-ref! node->n-preblock label 0) 1))]
           [else #f])))
     (define (n-preblock node)
       (dict-ref node->n-preblock node 0))
     (letrec ([jmp-handler
               (lambda (node)
                 (foldr
                  (lambda (instr accu)
                    (match instr
                      [(Jmp label)
                       #:when (not (eq? label 'conclusion))
                       (if (eq? (n-preblock label) 1)
                           (let ([accu^ (append (jmp-handler label) accu)])
                             (dict-remove! node->instrs label)
                             accu^)
                           (begin (jmpif-handler label)
                                  (cons instr accu)))]
                      [(JmpIf cc label)
                       #:when (not (eq? label 'conclusion))
                       (begin (jmpif-handler label)
                              (cons instr accu))]
                      [else (cons instr accu)]))
                  '()
                  (dict-ref node->instrs node)))]
              [jmpif-handler
               (lambda (node)
                 (define instrs
                   (foldr
                    (lambda (instr accu)
                      (match instr
                        [(Jmp label)
                         #:when (not (eq? label 'conclusion))
                         (if (eq? (n-preblock label) 1)
                             (let ([accu^ (append (jmp-handler label) accu)])
                               (dict-remove! node->instrs label)
                               accu^)
                             (begin (jmpif-handler label)
                                    (cons instr accu)))]
                        [(JmpIf cc label)
                         #:when (not (eq? label 'conclusion))
                         (begin (jmpif-handler label)
                                (cons instr accu))]
                        [else (cons instr accu)]))
                    '()
                    (dict-ref node->instrs node)))
                 (dict-set! node->instrs node instrs))])
       (jmpif-handler 'start)
       (define labs^
         (map (lambda (label-instrs)
                (let ([label (car label-instrs)]
                      [instrs (cdr label-instrs)])
                  (cons label (Block (Block-info (dict-ref labs label)) instrs))))
              (dict->list node->instrs)))
       (X86Program info labs^))]))

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (match p
    [(X86Program info (list (cons label (Block '() instructions))))
     (let* ([vars-size 0]
            [vars-locations
             (map (lambda (var-type)
                    (set! vars-size (+ vars-size 8))
                    (cons (Var (car var-type))     ;; make it more convenient to access the stack
                          (Deref 'rbp (- vars-size))))  ;; locations of variables in instructions later.
                  (dict-ref info 'locals-types))]
            [total-size (if (= (modulo vars-size 16) 0) (+ vars-size 16) (+ vars-size 24))]
            [assigned-instrs
             (map (lambda (instr)
                    (match instr
                      [(Instr one-arg `(,arg))
                       (Instr one-arg `(,(dict-ref vars-locations arg arg)))]
                      [(Instr two-args `(,arg1 ,arg2))
                       (Instr two-args
                              `(,(dict-ref vars-locations arg1 arg1)
                                ,(dict-ref vars-locations arg2 arg2)))]
                      [else instr]))
                  instructions)])
       (X86Program
        (cons (cons 'stack-space total-size) info)
        (list (cons label (Block '() assigned-instrs)))))]))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (match p
    [(X86Program info labs)
     (define labs^
       (for/list ([lab labs])
         (match lab
           [(cons label (Block binfo instructions))
            (let ([patched-instrs
                   (foldr (lambda (instr accu)
                            (match instr
                              [(Instr 'movq `(,arg1 ,arg2))
                               #:when (equal? arg1 arg2)
                               accu]
                              [(Instr 'movzbq `(,arg1 ,arg2))
                               #:when (not (Reg? arg2))
                               (cons (Instr 'movq `(,arg2 ,(Reg 'rax)))
                                     (cons (Instr 'movzbq `(,arg1 ,(Reg 'rax)))
                                           accu))]
                              [(Instr 'cmpq `(,arg1 ,arg2))
                               #:when (Imm? arg2)
                               (cons (Instr 'movq `(,arg2 ,(Reg 'rax)))
                                     (cons (Instr 'cmpq `(,arg1 ,(Reg 'rax)))
                                           accu))]
                              [(Instr two-args `(,arg1 ,arg2))
                               #:when (and (or (Deref? arg1) (Global? arg1))
                                           (or (Deref? arg2) (Global? arg2)))
                               (cons (Instr 'movq `(,arg1 ,(Reg 'rax)))
                                     (cons (Instr two-args `(,(Reg 'rax) ,arg2))
                                           accu))]
                              [else (cons instr accu)]))
                          '()
                          instructions)])
              (cons label (Block binfo patched-instrs)))])))
     (X86Program info labs^)]))

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info labs)
     (let* ([used-callee (set->list (dict-ref info 'used-callee))]
            [num-procedure-spills (dict-ref info 'num-procedure-spills)]
            [num-root-spills (dict-ref info 'num-root-spills)]
            [callee_spilled  (+ (* 8 (length used-callee))
                             (* 8 num-procedure-spills))]
            [alignment (- (if (= (modulo callee_spilled 16) 0)
                              callee_spilled
                              (+ callee_spilled 8))
                          (* (length used-callee) 8))]
            [pushing-callee
             (for/list ([callee used-callee])
               (Instr 'pushq `(,callee)))]
            [poping-callee
             (for/list ([callee (reverse used-callee)])
               (Instr 'popq `(,callee)))]
            [zero-out
             (for/list ([i (in-naturals 0)]
                        #:break (>= i num-root-spills))
               (Instr 'movq `(,(Imm 0) ,(Deref 'r15 (* i 8)))))]
            [bumping-upward
             (if (> num-root-spills 0)
                 `(,(Instr 'addq `(,(Imm (* 8 num-root-spills)) ,(Reg 'r15))))
                 '())]
            [bumping-downward
             (if (> num-root-spills 0)
                 `(,(Instr 'subq `(,(Imm (* 8 num-root-spills)) ,(Reg 'r15))))
                 '())]
            [main
             (cons 'main (Block '() (append
                                     `(,(Instr 'pushq `(,(Reg 'rbp)))
                                       ,(Instr 'movq `(,(Reg 'rsp) ,(Reg 'rbp))))
                                     ;; callee-saved registers
                                     pushing-callee
                                     ;; stack-stored variables + alignment fill
                                     (if (not (= alignment 0))
                                         `(,(Instr 'subq `(,(Imm alignment) ,(Reg 'rsp))))
                                         '())
                                     `(,(Instr 'movq `(,(Imm 65536) ,(Reg 'rdi)))
                                       ,(Instr 'movq `(,(Imm 65536) ,(Reg 'rsi)))
                                       ,(Callq 'initialize 2)
                                       ,(Instr 'movq `(,(Global 'rootstack_begin) ,(Reg 'r15))))
                                     zero-out
                                     bumping-upward
                                     `(,(Jmp 'start)))))]
            [conclusion
             (cons 'conclusion (Block '() (append
                                           bumping-downward
                                           ;; stack-stored variables + alignment fill
                                           (if (not (= alignment 0))
                                               `(,(Instr 'addq `(,(Imm alignment) ,(Reg 'rsp))))
                                               '())
                                           ;; callee-saved registers
                                           poping-callee
                                           `(,(Instr 'popq `(,(Reg 'rbp)))
                                             ,(Retq)))))])
       (X86Program info (cons main (cons conclusion labs))))]))

;; reference to textbook page23 to figure out how
;; the testing of this compiler works.
(define compiler-passes
  `( ("shrink" ,shrink ,interp-Lfun-prime ,type-check-Lfun)
     ("uniquify" ,uniquify ,interp-Lfun-prime ,type-check-Lfun)
     ("reveal functions" ,reveal_functions ,interp-Lfun-prime ,type-check-Lfun)
     ("limit functions" ,limit_functions ,interp-Lfun-prime ,type-check-Lfun)
     ;; ("uncover get!" ,uncover-get! ,interp-Lfun-prime ,type-check-Lfun)
     ))

;; (define compiler-passes
;;   `( ("shrink" ,shrink ,interp-Lvec ,type-check-Lvec)
;;      ("uniquify" ,uniquify ,interp-Lvec ,type-check-Lvec)
;;      ("uncover get!" ,uncover-get! ,interp-Lvec ,type-check-Lvec)
;;      ("expose allocation" ,expose_allocation ,interp-Lvec-prime ,type-check-Lvec)
;;      ("remove complex opera*" ,remove-complex-opera* ,interp-Lvec-prime ,type-check-Lvec)
;;      ("explicate control" ,explicate-control ,interp-Cvec ,type-check-Cvec)
;;      ("instruction selection" ,select-instructions ,interp-pseudo-x86-2)
;;      ("uncover live" ,uncover_live ,interp-pseudo-x86-2)
;;      ("build interference" ,build_interference ,interp-pseudo-x86-2)
;;      ("allocate registers" ,allocate_registers ,interp-pseudo-x86-2)
;;      ("remove jumps" ,remove_jumps ,interp-pseudo-x86-2)
;;      ("patch instructions" ,patch-instructions ,interp-x86-2)
;;      ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-2)
;;      ))
