; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
(defdata base (range integer (2 <= _))) ;; base 1 is simply a bunch of ones repeated (like tally marks), so bases start at 2
(defdata denominator (or (list pos) (cons nat denominator))) ;; denominator cannot consist solely of a nat (otherwise it could be 0), but it can have nats in its digits
(defdata base-num (or nil denominator)) ;; numerator and denominator are defined differently, as numerator can be 0, while denom. can't
(defdata base-fraction (list base base-num denominator)) ;; first digit is base; second is numerator; third is denominator
(defdata lop (listof pos))

;; helper function for base-n-to-dec; uses an accumulator to keep track of the digit
(definec base-n-to-dec-help (n :base-num base :base acc :nat) :nat
  (if (endp n) 0
    (+ (* (first n) (expt base acc)) (base-n-to-dec-help (rest n) base (1+ acc)))))

;; converts a number in base n to a nat in decimal
(definec base-n-to-dec (n :base-num base :base) :nat
  (base-n-to-dec-help n base 0))

;; used in the hw a lot, needs no introduction
(definec in2 (a :all X :tl) :bool
  (and (consp X)
       (or (== a (first X))
           (in2 a (rest X)))))

;; the bulk of my recursion takes place here. checks if the denominator's prime factorization can be written solely using the prime factors of the base
(definec new-base-will-terminate-help (denom :pos base-factors :lop) :bool
  :ic (not (in2 1 base-factors))
  (cond ((equal denom 1) t)
        ((equal base-factors nil) nil)
        ((equal 0 (mod denom (first base-factors))) (new-base-will-terminate-help (/ denom (first base-factors)) base-factors))
        (t (new-base-will-terminate-help denom (rest base-factors)))))

;; checks if every number between 2 and itself is prime
(definec primep-help (n :nat acc :pos) :bool
  :ic (<= acc n)
  (if (equal n acc) t
    (and (not (equal (mod n acc) 0)) (primep-help n (1+ acc)))))

;; checks if a number greater than or equal to 2 is prime
(definec primep (n :nat) :bool
  :ic (>= n 2)
  (primep-help n 2))

;; loops through all numbers between 2 and itself and checks if they are prime and divisible by the number
(definec prime-factors-help (num :pos acc :pos) :lop
  :ic (and (<= acc num) (>= acc 2))
  :oc (not (in2 1 (prime-factors-help num acc)))
  (cond ((equal num acc) (if (primep acc) (list acc) nil))
        ((equal (mod num acc) 0) (if (primep acc) (cons acc (prime-factors-help num (1+ acc))) (prime-factors-help num (1+ acc))))
        (t (prime-factors-help num (1+ acc)))))

;; finds the prime factors of a number
(definec prime-factors (num :pos) :lop
  :ic (>= num 2)
  :oc (not (in2 1 (prime-factors num)))
  (prime-factors-help num 2))

;; divides the numerator and the denominator by their shared factors until it is no longer possible to do so,
;; then returns the denominator
(definec new-denom-help (num :pos denom :pos numer-factors :lop) :pos
  :ic (and (< num denom) (not (in2 1 numer-factors)))
  (cond ((equal numer-factors nil) denom)
        ((and (equal 0 (mod denom (first numer-factors))) (equal 0 (mod num (first numer-factors)))) 
           (new-denom-help (/ num (first numer-factors)) (/ denom (first numer-factors)) numer-factors))
        (t (new-denom-help num denom (rest numer-factors)))))

;; simplifies the denominator using WikiHow rules (see my paper for more detail)
(definec new-denom-simple (num :nat denom :pos) :pos
  :ic (< num denom)
  (cond ((not (>= num 2)) denom)
        ((not (posp num)) denom)
        ((< denom 2) denom)
        ((primep denom) denom)
        ((natp (/ denom num)) (/ denom num))
        ((equal (- denom num) 1) denom)
        (t (new-denom-help num denom (prime-factors num)))))

;; checks if the number is in base n (used only for the input contract below)
(definec base-np (bn :base-num base :base) :bool
  (if (equal bn nil) t (and (< (first bn) base) (base-np (rest bn) base))))

;; the crown jewel. checks if a base-m fraction can convert to a terminating base-n decimal (returns nil if the decimal recurs)
(definec new-base-will-terminate (bf :base-fraction new-base :base) :bool
  :ic (and (posp (base-n-to-dec (first (rest (rest bf))) (first bf)))
           (base-np (first (rest bf)) (first bf))
           (base-np (first (rest (rest bf))) (first bf))
           (> (base-n-to-dec (first (rest (rest bf))) (first bf)) (base-n-to-dec (first (rest bf)) (first bf))))
  (let ((new-num (base-n-to-dec (first (rest bf)) (first bf)))
        (new-denom (base-n-to-dec (first (rest (rest bf))) (first bf))))
    (if (equal new-num 0) t
      (new-base-will-terminate-help (new-denom-simple new-num new-denom) (prime-factors new-base)))))#|ACL2s-ToDo-Line|#
