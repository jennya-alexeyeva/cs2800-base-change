(defdata base (range integer (2 <= _)))
(defdata denominator (or (list pos) (cons nat denominator)))
(defdata base-num (or nil denominator))
(defdata base-fraction (list base base-num denominator))
(defdata lop (listof pos))

(definec base-n-to-dec-help (n :base-num base :base acc :nat) :nat
  (if (endp n) 0
    (+ (* (first n) (expt base acc)) (base-n-to-dec-help (rest n) base (1+ acc)))))

(definec base-n-to-dec (n :base-num base :base) :nat
  (base-n-to-dec-help n base 0))

(definec primep-help (n :nat acc :pos) :bool
  :ic (<= acc n)
  (if (equal n acc) t 
    (and (not (equal (mod n acc) 0)) (primep-help n (1+ acc)))))

(definec primep (n :nat) :bool
  (if (<= n 2) t (primep-help n 2)))

(definec in2 (a :all X :tl) :bool
  (and (consp X)
       (or (== a (first X))
           (in2 a (rest X)))))

(definec greatest-common (l1 :lop l2 :lop) :pos
  (cond ((endp l1) 1)
        ((in2 (first l1) l2) (first l1))
        (t (greatest-common (rest l1) l2))))

(definec all-factors-acc (num :pos acc :pos) :lop
  :ic (<= acc num)
  (cond ((equal num acc) (list acc))
        ((equal (mod num acc) 0) (cons acc (all-factors-acc num (+ 1 acc))))
        (t (all-factors-acc num (+ 1 acc)))))

(definec all-factors (num :nat) :lop
  (if (equal num 0) nil (all-factors-acc num 1)))

(definec app2 (a :tl b :tl) :tl
  (if (endp a)
    b
    (cons (first a) (app2 (rest a) b))))

(definec rev2 (x :lop) :lop
  (if (endp x)
    nil
    (app2 (rev2 (rest x)) (list (first x)))))

(definec gcf (num :nat denom :nat) :pos
  :ic (and (>= num 2) (>= denom 2))
  (greatest-common (rev2 (all-factors num)) (all-factors denom)))
  
  
(definec new-denom-simple (new-num :nat new-denom :pos) :pos
  (cond ((< new-num 2) new-denom)
        ((< new-denom 2) new-denom)
        ((primep new-denom) new-denom)
        ((natp (/ new-denom new-num)) (/ new-denom new-num))
        ((equal (- new-denom new-num) 1) new-denom)
        (t (ceiling new-denom (gcf new-num new-denom)))))

(definec filter-prime (factors :lop) :lop
  (cond ((endp factors) nil)
        ((primep (first factors)) (cons (first factors) (filter-prime (rest factors))))
        (t (filter-prime (rest factors)))))

(definec all-prime-factors (num :nat) :lop
  :ic (>= num 2)
  (filter-prime (all-factors num)))

(definec in2-all (a :tl b :tl) :bool
  (or (endp a) (and (in2 (first a) b) (in2-all (rest a) b))))

(definec new-base-will-terminate-help (denom :pos base :base) :bool
  (if (equal denom 1) t
  (in2-all (all-prime-factors denom) (all-prime-factors base))))

(definec new-base-will-terminate (bf :base-fraction new-base :base) :bool
  :ic (posp (base-n-to-dec (first (rest (rest bf))) (first bf)))
  (let ((new-num (base-n-to-dec (first (rest bf)) (first bf)))
        (new-denom (base-n-to-dec (first (rest (rest bf))) (first bf))))
    (if (equal new-num 0) t
   (new-base-will-terminate-help (new-denom-simple new-num new-denom) new-base))))
