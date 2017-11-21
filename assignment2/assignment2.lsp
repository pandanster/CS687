
;;;PREDEFINED FUNCTIONS ARE BEING PLACED IN HERE


;;; Useful Functions and Macros

(defmacro swap (elt1 elt2)
  "Swaps elt1 and elt2, using SETF.  Returns nil."
  (let ((temp (gensym)))
    `(let ((,temp ,elt1))
       (setf ,elt1 ,elt2)
       (setf ,elt2 ,temp)
       nil)))

(defmacro while (test return-value &body body)
  "Repeatedly executes body as long as test returns true.
Then evaluates and returns return-value"
  `(progn (loop while ,test do (progn ,@body)) ,return-value))

(defun random-elt (sequence)
  "Returns a random element from sequence"
  (elt sequence (random (length sequence))))

(defun random? (&optional (prob 0.5))
  "Tosses a coin of prob probability of coming up heads,
then returns t if it's heads, else nil."
  (< (random 1.0) prob))

(defun generate-list (num function &optional no-duplicates)
  "Generates a list of size NUM, with each element created by
  (funcall FUNCTION).  If no-duplicates is t, then no duplicates
are permitted (FUNCTION is repeatedly called until a unique
new slot is created).  EQUALP is the test used for duplicates."
  (let (bag)
    (while (< (length bag) num) bag
      (let ((candidate (funcall function)))
	(unless (and no-duplicates
		          (member candidate bag :test #'equalp))
	    (push candidate bag))))))
;;;;;; TOP-LEVEL EVOLUTIONARY COMPUTATION FUNCTIONS 


;;; TOURNAMENT SELECTION
(defparameter *tournament-size* 7)
(defun tournament-select-one (population fitnesses)
  "Does one tournament selection and returns the selected individual."
  (let ((fittest (random (length population))))
    (dotimes (i *tournament-size*)
      (let ((candidate (random (length population))))
	(if (> (* 1 (elt fitnesses candidate)) (* 1 (elt fitnesses fittest)))
	    (setf fittest candidate))))
    (elt population fittest)))



(defun tournament-selector (num population fitnesses)
  "Does NUM tournament selections, and puts them all in a list"
  (let ((next-gen '()))
    (dotimes (i num)
      (setf next-gen (append next-gen (list (tournament-select-one population fitnesses)))))
    next-gen))

(defun evolve (generations pop-size
			          &key setup creator selector modifier evaluator printer)
  "Evolves for some number of GENERATIONS, creating a population of size
POP-SIZE, using various functions"
  ;; The functions passed in are as follows:
  ;;(SETUP)                     called at the beginning of evolution, to set up
  ;;                            global variables as necessary
  ;;(CREATOR)                   creates a random individual
  ;;(SELECTOR num pop fitneses) given a population and a list of corresponding fitnesses,
  ;;                            selects and returns NUM individuals as a list.
  ;;                            An individual may appear more than once in the list.
  ;;(MODIFIER ind1 ind2)        modifies individuals ind1 and ind2 by crossing them
  ;;                            over and mutating them.  Returns the two children
  ;;                            as a list: (child1 child2).  Nondestructive to
  ;;                            ind1 and ind2.
  ;;(PRINTER pop fitnesses)     prints the best individual in the population, plus
  ;;                            its fitness, and any other interesting statistics
  ;;                            you think interesting for that generation.
  ;;(EVALUATOR individual)      evaluates an individual, and returns its fitness.
  ;;Pop will be guaranteed to be a multiple of 2 in size.
  ;;
  ;; HIGHER FITNESSES ARE BETTER

  ;; your function should call PRINTER each generation, and also print out or the
  ;; best individual discovered over the whole run at the end, plus its fitness
  ;; and any other statistics you think might be nifty.

    ;;; IMPLEMENT M
  (funcall setup)
  (let ((pop '()) (fitnesses '()) (next-gen '()) (parent1 '()) (parent2 '()))
    (dotimes (i pop-size)
      (setf pop (append pop (cons (funcall creator) nil))))
    (dotimes (i generations)
      (setf fitnesses (mapcar evaluator pop))
      (setf parent1 (funcall  selector (/ pop-size 2) pop fitnesses))
      (setf parent2 (funcall selector (/ pop-size 2) pop fitnesses))
      (setf pop (mapcar modifier parent1 parent2))
      (setf pop (append (mapcar #'first pop) (mapcar #'second pop)))
      (funcall printer pop fitnesses))))


(defun simple-printer (pop fitnesses)  ;; I'm nice and am providing this for you.  :-)
  "Determines the individual in pop with the best (highest) fitness, then
prints that fitness and individual in a pleasing manner."
  (let (best-ind best-fit)
    (mapcar #'(lambda (ind fit)
		(when (or (not best-ind)
			    (< best-fit fit))
		    (setq best-ind ind)
		      (setq best-fit fit))) pop fitnesses)
    (format t "~%Best Individual of Generation...~%Fitness: ~a~%Individual:~a~%"
	        best-fit best-ind)
    fitnesses))

(defparameter *boolean-vector-length* 100) 
(defparameter *boolean-problem* :max-ones) 
;; perhaps other problems might include...  
 
(defun boolean-vector-creator () 
  "Creates a boolean-vector *boolean-vector-length* in size, filled with 
random Ts and NILs, or with random 1s and 0s, your option." 
    ;;; IMPLEMENT ME 
  (let((boolean-vector (make-array *boolean-vector-length*))) 
    (dotimes (i *boolean-vector-length*) 
      (setf (aref boolean-vector i) (random 2))) 
    boolean-vector)) 
 
 
(defparameter *boolean-crossover-probability* 0.2) 
(defparameter *boolean-mutation-probability* 0.01) 
(defun boolean-vector-modifier (ind1 ind2) 
  "Copies and modifies ind1 and ind2 by crossing them over with a uniform crossover, 
then mutates the children.  *crossover-probability* is the probability that any 
given allele will crossover.  *mutation-probability* is the probability that any 
given allele in a child will mutate.  Mutation simply flips the bit of the allele." 
 
    ;;; IMPLEMENT ME 
  (let ((child1 (make-array (length ind1))) (child2 (make-array (length ind2)))) 
    (dotimes (i (length ind1)) 
      (if (< (random 1.0) *boolean-crossover-probability*) 
      (progn 
        (setf (aref child1 i) (aref ind2 i)) 
        (setf (aref child2 i) (aref ind1 i)))) 
      (if (< (random 1.0) *boolean-mutation-probability*) 
        (setf (aref child1 i) (if(= (aref child1 i) 0) 1 0));;flip bit for child 2 
        (setf (aref child2 i) (if(= (aref child2 i) 0) 1 0)))) 
    (list child1 child2)));;flip bit for child 2 
 
(defun boolean-vector-evaluator (ind1) 
  "Evaluates an individual, which must be a boolean-vector, and returns 
its fitness." 
(let ((sum 0))    ;;implementation for max ones 
    ;;; IMPLEMENT ME 
    (dotimes (i (length ind1)) 
    (setf sum (+ sum (aref ind1 i)))) 
    sum)) 

;;;Working on the floating point vector problem
(defun get1or-1 ()
  (if (> (random 1.0) 0.5)
      '1
      '-1))

(defparameter *float-vector-length* 100)

(defparameter *float-problem* :rastrigin)
(defparameter *float-min* -5.12)  ;; these will change based on the problem
(defparameter *float-max* 5.12)   ;; likewise

(defun float-vector-creator ()
  "Creates a floating-point-vector *float-vector-length* in size, filled with
random numbers in the range appropriate to the given problem"
  (let ((population-vector (make-array *float-vector-length*)))
    (dotimes (i *float-vector-length*)
      (setf (aref population-vector i) (* (get1or-1) (random 5.12))))
    population-vector))


(defparameter *float-crossover-probability* 0.2)
(defparameter *float-mutation-probability* 0.1)   ;; I just made up this number
(defparameter *float-mutation-variance* 0.01)     ;; I just made up this number

;;;Tweak the given vector by Gaussian convolution

(defun gaussian-mutation(vector min max p variance)
  "Tweaks the given vector by adding noice with gaussian convulution"
  (let ((tweaked (make-array (length vector))))
    (dotimes (i (length vector))
      (if (> p (random 1.0))
	  (let ((noise (random variance)))
	    (while (or (> (+ (aref vector i) noise) max) (< (+ (aref vector i) noise) min))
	      (setf noise (random variance)))
	    (setf (aref tweaked i) (+ (aref vector i) noise)))))
    tweaked))
   

(defun float-vector-modifier (ind1 ind2)
  "Copies and modifies ind1 and ind2 by crossing them over with a uniform crossover,
then mutates the children.  *crossover-probability* is the probability that any
given allele will crossover.  *mutation-probability* is the probability that any
given allele in a child will mutate.  Mutation does gaussian convolution on the allele."

    ;;; IMPLEMENT ME
    ;;; Note: crossover is probably identical to the bit-vector crossover
    ;;; See "Gaussian Convolution" (Algorithm 11) in the book for mutation
  (let ((child1 (make-array (length ind1))) (child2 (make-array (length ind2))))
    (dotimes (i (length ind1))
      (if (> (random 1.0) *float-crossover-probability*)
	  (progn
	    (setf (aref child1 i) (aref ind2 i))
	    (setf (aref child2 i) (aref ind1 i)))
	  (progn
	    (setf (aref child1 i) (aref ind1 i))
	    (setf (aref child2 i) (aref ind2 i)))))
    (list (gaussian-mutation child1 *float-min* *float-max* *float-mutation-probability* *float-mutation-variance*) (gaussian-mutation child2 *float-min* *float-max* *float-mutation-probability* *float-mutation-variance*))))

(defun rastrigin-evaluator(ind)
  (let ((fitness '0) (n (length ind)))
    (dotimes (i (length ind))
      (setf fitness (+ fitness (- (* (aref ind i) (aref ind i)) (* 10 (cos (* 2 pi (aref ind i))))))))
    (+ fitness (* 10 n))))
(defun float-vector-sum-evaluator(ind)
  (rastrigin-evaluator ind))

(defun float-vector-sum-setup(length min max problem cross-over-probability mutation-probability mutation-variance)

  (setf *float-vector-length* length)
  (setf *float-problem* problem)
  (setf *float-min* min)
  (setf *float-max* max)
  (setf *float-crossover-probability* cross-over-probability)
  (setf *float-mutation-probability* mutation-probability)
  (setf *float-mutation-variance* mutation-variance))
  
(defun make-queue ()
  "Makes a random-queue"
  (make-array '(0) :adjustable t :fill-pointer t))
(defun enqueue (elt queue)
  "Enqueues an element in the random-queue"
  (progn (vector-push-extend elt queue) queue))
(defun queue-empty-p (queue)
  "Returns t if random-queue is empty"
  (= (length queue) 0))
(defun random-dequeue (queue)
  "Picks a random element in queue and removes and returns it.
Error generated if the queue is empty."
  (let ((index (random (length queue))))
    (swap (elt queue index) (elt queue (1- (length queue))))
    (vector-pop queue)))
(defparameter *nonterminal-set* '())
(defparameter *terminal-set* '())

(defun ptc2(size)
  "If size=1, just returns a random terminal.  Else builds and
returns a tree by repeatedly extending the tree horizon with
nonterminals until the total number of nonterminals in the tree,
plus the number of unfilled slots in the horizon, is >= size.
Then fills the remaining slots in the horizon with terminals.
Terminals like X should be added to the tree
in function form (X) rather than just X."
  (if (eql size 1)
      (return-from ptc2 (list (random-elt *terminal-set*))))
  (let ((tree (make-queue)) (count 0)(root (make-queue)) (remaining-slots 0))
    (loop while (> size (+ count (length tree)))
       do (progn
	    (let ((curr-elt (random-elt *nonterminal-set*)))
	      (if (queue-empty-p tree)
		  (progn
		    (enqueue curr-elt tree)
		    (enqueue (list (first curr-elt)) root)
		    (setf count (1+ count)))
		  (progn
		    (let ((slot (random (length tree))))
		      (loop while (eql (second (elt tree slot)) 0)
			 do (progn
			      (setf slot (random (length tree)))))
		      (enqueue curr-elt tree)
		      (enqueue (list (first curr-elt)) root)
		      (setf (elt tree slot) (list (first (elt tree slot)) (1- (second (elt tree slot)))))
		      (setf (elt root slot) (append (elt root slot) (cons (1- (length tree)) nil)))
		      (setf count (1+ count))))))))
	 (dotimes (i (length tree))
	   (setf remaining-slots (+ remaining-slots (second (elt tree i)))))
    (loop while (> remaining-slots 0)
       do (let ((slot (random (length tree))))
	  (loop while (or (eql (length (elt tree slot)) 1) (eql (second (elt tree slot)) 0))
	      do (progn
		(setf slot (random (length tree)))))
	  (let ((curr-elt (random-elt *terminal-set*)))
	    (enqueue  (list curr-elt) tree)
	    (enqueue (list curr-elt) root)
	    (setf (elt tree slot) (list (first (elt tree slot)) (1- (second (elt tree slot)))))
	    (setf (elt root slot) (append (elt root slot) (cons (1- (length tree)) nil)))))
	 (setf remaining-slots (1- remaining-slots)))
    (let ((tree-size (1- (length root))))
      (loop while (>= tree-size 0)
	  do (if (> (length (elt root tree-size)) 1)
	      (let ((temp '()) (curr-elt (elt root tree-size)))
		(dotimes (i (length (elt root tree-size)))
		  (if (= i 0)
		      (setf temp (append temp (list (first curr-elt))))
		      (setf temp (append temp (list (elt root (elt curr-elt i)))))))
		(setf (elt root tree-size) temp)))
	(setf tree-size (1- tree-size))))
    (elt root 0)))



(defparameter *size-limit* 20)

(defun gp-creator()
  (let ((tree-size (random *size-limit*)))
    (loop while (eql tree-size 0)
	while (setf tree-size (random *size-limit*)))
    (ptc2 tree-size)))
		  
(defun num-nodes (tree)
  (if (or (not (consp tree))(=  (length tree) 1))
      '0
      (let ((node-count 0))
	(dolist (i tree)
	  (setf node-count (+ node-count (num-nodes i))))
	(1+ node-count))))
(defun get-tree-size(tree size)
  (dolist (i tree)
    (if (consp i)
	(setf size (get-tree-size i size))
	(setf size (1+ size))))
  size)

(defun nth-subtree-parent-helper (tree count n)
  ;(format t "Received tree ~A ~%" tree)
  (let ((child-count -1))
    (dolist (i tree)
      (if (equal count n)
	  (return-from nth-subtree-parent-helper (list tree child-count))
	  (progn
	    (if (consp i)
		(let ((received (nth-subtree-parent-helper i count n)))
		  (if (consp received)
		      (return-from nth-subtree-parent-helper received)
		      (progn
			(setf count (+ count  (get-tree-size i 0)))
			(setf child-count (1+ child-count)))))
		(progn
		  (setf count (1+ count))
		  (setf child-count (1+ child-count)))))))
	(- n count)))

(defun nth-subtree-parent(tree n)
  ;(format t "I am being called ~%")
  (nth-subtree-parent-helper tree -1 n))

(defparameter *mutation-size-limit* 10)

(defun make-deep-copy (tree)
  (let ((copy-tree '()))
    (dolist (i tree)
      (if (consp i)
	  (setf copy-tree (append copy-tree (cons (make-deep-copy i) nil) ))
	  (setf copy-tree (append copy-tree (cons i nil)))))
    copy-tree))

(defun copy-modify-tree(tree fsub-tree msub-tree)
  (let ((child '()))
    (dolist (i tree)
     ;(format t "list element: ~A compared: ~A ~%" i (first fsub-tree))
      (if (and (consp i) (equal i (first fsub-tree)))
	  (let ((temp '()) (child-count -1))
	    (dolist (j i)
	      (if(equal child-count (second fsub-tree))
		 (setf temp (append temp (cons  msub-tree nil)))
		 (progn
		   (if (consp j)
		       (setf temp (append temp (cons (make-deep-copy j) nil)))
		       (setf temp (append temp (cons j nil))))))
	      (setf child-count (1+ child-count)))
	    (setf child (append child (cons temp nil))))
	  (if (consp i)
	      (setf child (append child (cons (copy-modify-tree i fsub-tree msub-tree) nil)))
	      (setf child (append child (cons i nil))))))
    child))
		   
(defun gp-modifier (ind1 ind2)
  ;(format t "Received ind1 : ~A ind2 :~A ~%" ind1 ind2)
  (if (random?)
      (let ((child1 '()) (child2 '()) (subtree1 '()) (subtree2 '()))
	(setf subtree1 (nth-subtree-parent ind1 (random (get-tree-size ind1 0) )))
	(setf subtree2 (nth-subtree-parent ind2 (random (get-tree-size ind2 0))))
	(if (and (consp subtree2) (consp subtree1))
	    (progn
	      (setf child1 (copy-modify-tree ind1 subtree1 (nth (+ (second subtree2) 1) (first subtree2))))
	      (setf child2 (copy-modify-tree ind2 subtree2 (nth (+ (second subtree1) 1) (first subtree1)))))
	    (progn
	      (setf child1 (make-deep-copy ind1))
	      (setf child2 (make-deep-copy ind2))))
	(list child1 child2))
      (let ((child1 '()) (child2 '()) (subtree1 '()) (subtree2 '()))
	(setf subtree1 (nth-subtree-parent ind1 (random (get-tree-size ind1 0))))
	(setf subtree2 (nth-subtree-parent ind2 (random (get-tree-size ind2 0))))
	(if (consp subtree1)
	    (setf child1 (copy-modify-tree ind1 subtree1 (ptc2 (1+ (random 5)))))
	    (setf child1 (make-deep-copy ind1)))
	(if (consp subtree2)
	    (setf child2 (copy-modify-tree ind2 subtree2 (ptc2 (1+ (random 5)))))
	    (setf child2 (make-deep-copy ind2)))
	(list child1 child2))))
	

;;; GP SYMBOLIC REGRESSION SETUP
;;; (I provide this for you)

(defparameter *num-vals* 20)
(defparameter *vals* nil) ;; gets set in gp-setup

(defun gp-symbolic-regression-setup ()
  "Defines the function sets, and sets up vals"

  (setq *nonterminal-set* '((+ 2) (- 2) (* 2) (% 2) (sin 1) (cos 1) (exp 1)))
  (setq *terminal-set* '(x))

  (setq *vals* nil)
  (dotimes (v *num-vals*)
    (push (1- (random 2.0)) *vals*)))

(defun poly-to-learn (x) (+ (* x x x x) (* x x x) (* x x) x))

;; define the function set
(defparameter *x* nil) ;; to be set in gp-evaluator
(defun x () *x*)
(defun % (x y) (if (= y 0) 0 (/ x y)))  ;; "protected division"
;;; the rest of the functions are standard Lisp functions


(defun gp-symbolic-regression-evaluator (ind)
  (let ((z 0))
    (dolist (i *vals*)
      (setf *x* i)
      (setf z (+ z (abs (- (poly-to-learn *x*) (handler-case (eval ind) (error (condition) (format t "~%Warning, ~a" condition) most-positive-fixnum)))))))
    (/ 1 (1+ z))))

(defparameter *map-strs* '(
".###............................"
"...#............................"
"...#.....................###...."
"...#....................#....#.."
"...#....................#....#.."
"...####.#####........##........."
"............#................#.."
"............#.......#..........."
"............#.......#..........."
"............#.......#........#.."
"....................#..........."
"............#..................."
"............#................#.."
"............#.......#..........."
"............#.......#.....###..."
".................#.....#........"
"................................"
"............#..................."
"............#...#.......#......."
"............#...#..........#...."
"............#...#..............."
"............#...#..............."
"............#.............#....."
"............#..........#........"
"...##..#####....#..............."
".#..............#..............."
".#..............#..............."
".#......#######................."
".#.....#........................"
".......#........................"
"..####.........................."
         "................................"))

(defparameter *map-height* 32)
(defparameter *map-width* 32)
;; The four directions.  For relative direction, you might
;; assume that the ant always PERCEIVES things as if it were
;; facing north.
(defconstant *n* 0)
(defconstant *e* 1)
(defconstant *s* 2)
(defconstant *w* 3)

;;; some useful functions for you

(defun make-map (lis)
  "Makes a map out of a string-list such as *MAP-STRS*"
  (let ((map (make-array (list (length (first lis)) (length lis)))))
    (dotimes (y (length lis) map)
      (dotimes (x (length (elt lis y)))
  (setf (aref map x y)
              (cond ((equalp #\# (elt (elt lis y) x)) nil)
            (t t)))))))

(defun direction-to-arrow (dir)
  "Returns a character which represents a given direction -- might
be useful for showing the movement along a path perhaps..."
  (cond ((= dir *n*) #\x)
  ((= dir *s*) #\v)
  ((= dir *e*) #\>)
  (t #\<)))


(defun maparray (function array &optional (same-type nil))
  "Maps function over array in its major order.  If SAME-TYPE,
then the new array will have the same element type as the old
array; but if a function returns an invalid element then an error
may occur.  If SAME-TYPE is NIL, then the array will accommodate
any type."
  (let ((new-array (apply #'make-array (array-dimensions array)
          :element-type (if same-type
                    (array-element-type array)
                t)
            :adjustable (adjustable-array-p array)
              (if (vectorp array)
                  `(:fill-pointer ,(fill-pointer array))
              nil))))
    (dotimes (x (array-total-size array) new-array)
      (setf (row-major-aref new-array x)
          (funcall function (row-major-aref array x))))))

(defun print-map (map)
  "Prints a map, which must be a 2D array.  If a value in the map
is T (indicating a space), then a '.' is printed.  If a value in the map
is NIL (indicating a food pellet), then a '#' is printed.  If a value in
the map is anything else, then it is simply PRINTed.  This allows you to
consider spaces to be all sorts of stuff in case you'd like to print a
trail of spaces on the map for example.  Returns NIL."
  (let ((dim (array-dimensions map)))
    (dotimes (y (second dim) nil)
      (format t "~%")
      (dotimes (x (first dim))
  (format t "~a"
    (let ((v (aref map x y)))
        (cond ((equal v t) #\.)
        ((null v) #\#)
        (t v))))))))




(defmacro absolute-direction (relative-dir ant-dir)
  "If the ant is facing ANT-DIR, then converts the perceived
RELATIVE-DIR direction into an absolute ('true') direction
and returns that."
  `(mod (+ ,relative-dir ,ant-dir) 4))

(defmacro x-pos-at (x-pos absolute-dir &optional (steps 1))
  "Returns the new x position if one moved STEPS steps the absolute-dir
direction from the given x position.  Toroidal."
  `(mod (cond ((= (mod ,absolute-dir 2) *n*) ,x-pos)         ;; n or s
              ((= ,absolute-dir *e*) (+ ,x-pos ,steps))     ;; e
              (t (+ ,x-pos (- ,steps) *map-width*)))         ;; w
  *map-width*))

(defmacro y-pos-at (y-pos absolute-dir &optional (steps 1))
  "Returns the new y position if onee moved STEPS steps in the absolute-dir
direction from the given y position.  Toroidal."
  `(mod (cond ((= (mod ,absolute-dir 2) *e*) ,y-pos)        ;; e or w
              ((= ,absolute-dir *s*) (+ ,y-pos ,steps))     ;; s
              (t (+ ,y-pos (- ,steps) *map-height*)))       ;; n
  *map-height*))


(defparameter *current-move* 0 "The move # that the ant is at right now")
(defparameter *num-moves* 600 "How many moves the ant may make")
(defparameter *current-x-pos* 0 "The current X position of the ant")
(defparameter *current-y-pos* 0 "The current Y position of the ant")
(defparameter *current-ant-dir* *e* "The current direction the ant is facing")
(defparameter *eaten-pellets* 0 "How many pellets the ant has eaten so far")
(defparameter *map* (make-map *map-strs*) "The ant's map")


#|(defun if-i-move(direction)
  (let ((to-position '()))
    (cond ((eql direction *n*) (setf to-position (list (mod (1+ *current-x-pos*) *map-width*) *current-y-pos*)))
    ((eql direction *s*) (setf to-position (list (if (minusp (1- *current-x-pos*)) (+ (1- *current-x-pos*) *map-width*) (1- *current-x-pos*)) *current-y-pos*)))
    ((eql direction *w*) (setf to-position (list *current-x-pos* (if (minusp (1- *current-y-pos*)) (+ (1- *current-y-pos*) *map-width*) (1- *current-y-pos*)))))
    ((eql direction *e*) (setf to-position (list *current-x-pos* (mod (1+ *current-y-pos*) *map-width*)))))
    to-position))
|#

(defun food-found (x y)
  (not (aref *map* x y)))


(defmacro if-food-ahead (then else)
  "If there is food directly ahead of the ant, then THEN is evaluated,
else ELSE is evaluated"
  ;; because this is an if/then statement, it MUST be implemented as a macro.
  `(if (food-found (x-pos-at *current-x-pos* *current-ant-dir*) (y-pos-at *current-y-pos* *current-ant-dir*)) ,then ,else))


(defun progn2 (arg1 arg2)
    "Evaluates arg1 and arg2 in succession, then returns the value of arg2"
    (eval arg1)
    (eval arg2)
    arg2)  ;; ...though in artificial ant, the return value isn't used ... 

(defun progn3 (arg1 arg2 arg3)
  "Evaluates arg1, arg2, and arg3 in succession, then returns the value of arg3"
  (eval arg1)
  (eval arg2)
  (eval arg3)
  arg3)


(defun move()
  (if (< *current-move* *num-moves*)
      (let ((x  (x-pos-at *current-x-pos* *current-ant-dir*)) (y (y-pos-at *current-y-pos* *current-ant-dir*)))
  (if (food-found x y)
      (setf *eaten-pellets* (1+ *eaten-pellets*)))
  (setf (aref *map* *current-x-pos* *current-y-pos*) (direction-to-arrow *current-ant-dir*))
  (setf *current-x-pos* x)
  (setf *current-y-pos* y)
  (setf *current-move* (1+ *current-move*)))))

(defun left()
  (case *current-ant-dir*
    (0 (setf *current-ant-dir* *w*))
    (1 (setf *current-ant-dir* *n*))
    (3 (setf *current-ant-dir* *s*))
    (2 (setf *current-ant-dir* *e*)))
  (setf *current-move* (1+ *current-move*)))

(defun right()
  (case *current-ant-dir*
    (0 (setf *current-ant-dir* *e*))
    (1 (setf *current-ant-dir* *s*))
    (3 (setf *current-ant-dir* *w*))
    (2 (setf *current-ant-dir* *n*)))
  (setf *current-move* (1+ *current-move*)))

(defun gp-artificial-ant-setup ()
  "Sets up vals"
  (setq *nonterminal-set* '((if-food-ahead 2) (progn2 2) (progn3 3)))
  (setq *terminal-set* '(left right move))
  (setq *map* (make-map *map-strs*))
  (setq *current-move* 0)
  (setq *eaten-pellets* 0))


(defun gp-artificial-ant-evaluator (ind)
  "Evaluates an individual by putting it in a fresh map and letting it run
for *num-moves* moves.  The fitness is the number of pellets eaten -- thus
more pellets, higher (better) fitness."
  (setf *map* (make-map *map-strs*))
  (setf *current-move* 0)
  (setf *eaten-pellets* 0)
  (setf *current-x-pos* 0)
  (setf *current-y-pos* 0)
  (setf *current-ant-dir* *e*)
  (loop while (< *current-move* *num-moves*)
      do (eval ind))
  *eaten-pellets*)
