; Test with racket semantics.rkt
#lang racket

; Unit testing stuff for Racket
(require rackunit)
(require rackunit/text-ui)

(define const? number?)
(define var? symbol?)

; Create a struct to store addresses
(struct addr (loc))

; Environments are hashes
(define env? hash?)

; A predicate to determine whether an s expression is something we'd
; regard as an expression. This largely follows Fig 2 of the paper but
; diverges in that I use Scheme-style notation for some things.
(define (exp? e) 
  (match e
    [(? const?) #t]
    [(? var?) #t]
    ['̱'bot #t]
    ; Ref
    [`(ref ,(? exp?)) #t]
    ; ! e (I'm using deref rather than !)
    [`(deref ,(? exp?)) #t]
    ; e := e
    [`(set! ,(? exp?) ,(? exp?)) #t]
    ; ⟨ k ? e : e ⟩
    [`(mk-facet ,(? symbol?) ,(? exp?) ,(? exp?)) #t]
    ; lambda
    [`(lambda (,(? symbol?)) ,(? exp?)) #t]
    ; App
    [`(,(? exp?) ,(? exp?)) #t]))

; Predicate to determine if something is a value
(define (value? v)
  (match v
    [(? number?) #t]
    [(? addr?) #t]
    ['bot #t]
    ; Match a closure (cons of a lambda and an environment)
    [`((lambda (,(? symbol?)) ,body) . ,(? env?)) #t]))

; A function which returns a sequence of 1, 2, ...  (When called for
; the first time returns 1, then 2, ...). We use this for "allocating"
; addresses in the heap.
(define fresh 
  (let ([x 0])
    (lambda () (begin (set! x (+ x 1)) x))))

(define/contract (ev σ θ e)
  (hash? hash? exp? . -> . (cons/c hash? value?))
  (match e
    ; Bottom, be sure to put this case before var?
    ['bot (cons σ 'bot)]
    [(? const? e) (cons σ e)]
    [(? var? e) (cons σ (hash-ref θ e))]
    ; Comma here matches any var
    [`(lambda (,varname) ,body)
     (cons σ (cons e θ))]
    ; Note that we merge the two rules S-App / S-App-Bot here, since
    ; the antecedents of both rules are the same.
    [`(,e1 ,e2)
     (let* ([e1result (ev σ θ e1)]
            [σ1 (car e1result)]
            [fun (car (cdr e1result))]
            [θ1 (cdr (cdr e1result))]
            [e2result (ev σ1 θ e2)]
            [σ2 (car e2result)]
            [v1 (cdr e2result)])
       (match fun
         ; S-App
         [`(lambda (,var) ,body)
          (ev σ2 (hash-set θ1 var v1) body)]
         ; S-App-Bot
         ['bot (cons σ 'bot)]))]
    ; Ref
    [`(ref ,e)
     (let* ([eresult (ev σ θ e)]
            ; Notice the `addr`. This wraps the number returned by
            ; fresh in an `addr` struct.
            [new-address (addr (fresh))])
       (cons (hash-set (cdr eresult) new-address) new-address))]))

(define (evaluate e) (cdr (ev (hash) (hash) e)))

(run-tests
 (test-suite
  "Testing the big-step evaluation relation"
  (test-case "S-Const" (check-equal? (evaluate 3) 3))
  (test-case "S-Var" (check-equal? (cdr (ev (hash) (hash-set (hash) 'y 23) 'y)) 23))
  (test-case "S-Fun" (check-equal? (evaluate '(lambda (x) x)) (cons '(lambda (x) x) (hash))))
  (test-case "S-App-1" (check-equal?
              (evaluate '((lambda (x) ((lambda (y) 23) x)) 1))
              23))
  (test-case "S-App-2" (check-equal? (evaluate '((lambda (x) x) 1)) 1))
  ; Note that within the test you need to put bot rather than 'bot
  ; (this tripped me up).
  (test-case "S-App-Bot" (check-equal? (evaluate '((lambda (x) bot) 1)) 'bot))))
