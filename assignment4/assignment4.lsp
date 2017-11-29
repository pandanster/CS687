


(defun negate (predicate)
  "Negates a predicate.  Pretty simple!"
  (cons (not (first predicate)) (rest predicate)))
;;;;;; STRIPS OPERATORS
;;;;;; A strips operator has is described below.  Note that
;;;;;; UNIQ allows two operators with the same name, preconds
;;;;;; and effects to be in the plan at once.


(defstruct operator
   "Defines a strips operator consisting of
a NAME (a symbol or string),
a UNIQ gensym symbol assigned when the operator is added to the plan,
a list of PRECONDITIONS (predicates)
a list of EFFECTS ( predicates),

The resultant function MAKE-OPERATOR creates a *template*,
which is different from an instantiated operator actually in a plan.
Use instantiate-operator to create an operator from a template."
  name uniq preconditions effects)

;; Expect a possible warning here about redefinition
(defun copy-operator-2 (operator)
  "Copies the operator and assigns it a new unique gensym symbol to make
it unique as far as EQUALP is concerned.  Returns the copy."
  ;; I suggest you use this code to guarantee that the operator is properly
  ;; copied out of the templates.
  (let ((op (copy-structure operator)))
    (setf (operator-uniq op) (gensym))
    op))


;;;;;;; LINKS
;;;;;;; A link is a structure that specifies a causal link with a from-operator,
;;;;;;; a to-operator, and precondition of the to-operator involved
;;;;;;; (which is the SAME as the effect of the from-operator!)

(defstruct (link
	        (:print-function print-link))
  "FROM and TO are operators in the plan.
  PRECOND is the predicate that FROM's effect makes true in TO's precondition."
  from precond to)

(defun print-link (p stream depth)
  "Helper function to print link in a pretty way"
  (declare (ignorable depth))
  (format stream "#< (~a)~a -> (~a)~a : ~a >"
	    (when (link-from p) (operator-uniq (link-from p)))
	      (when (link-from p) (operator-name (link-from p)))
	        (when (link-to p) (operator-uniq (link-to p)))
		  (when (link-to p) (operator-name (link-to p)))
		  (link-precond p)))


;;;;;;; ORDERINGS
;;;;;;; An ordering is just a dotted pair of the form (before-op . after-op)
;;;;;;; where before-op and after-op are strips operators (instances of
;;;;;;; the OPERATOR structure).  The ordering specifies
;;;;;;; that before-op must come before after-op.


(defun print-ordering (p stream depth)
  "Helper function to print link in a pretty way"
  (declare (ignorable depth))
  (format stream "#[ (~a)~a -> (~a)~a ]"
	    (operator-uniq (first p))
	      (operator-name (first p))
	        (operator-uniq (rest p))
		  (operator-name (rest p))))

;;;;;;; PLANS
;;;;;;; A plan is a list of operators, a list of orderings, and a list of
(defstruct (plan (:print-function print-plan))
  "A collection of lists of operators, orderings, and links,
plus a pointer to the start operator and to the goal operator."
  operators orderings links start goal)

(defun print-plan (p stream depth)
  "Helper function print plan in a pretty way"
  (declare (ignorable depth))
  (format stream "#< PLAN operators: ~{~%~a~} ~%links: ~{~%~a~} ~%orderings: ~{~%~a~}~%>"
	    (plan-operators p) (plan-links p)
	      (mapcar #'(lambda (ordering)
			        (print-ordering ordering nil 0))
		      (plan-orderings p))))

(defun copy-plan-2 (plan)
  ;; I suggest you use this code to guarantee that the plan is copied
  ;; before you do any destructive coding on it.
  "Deep-copies the plan, and copies the operators, orderings, and links."
  (let ((p (copy-structure plan)))
    (setf (plan-operators p) (copy-tree (plan-operators p)))
    (setf (plan-orderings p) (copy-tree (plan-orderings p)))
    (setf (plan-links p) (copy-tree (plan-links p)))
    p))

;;;;;;;;; UTILITY FUNCTIONS
;;;;;;;;; I predict you will find these functions useful.

;;;; Reachable takes an association list and determines if you can reach
;;;; an item in the list from another item.  For example:
;;;;
;;;; (reachable '((a . b) (c . d) (b . c) (b . e) (e . a)) 'e 'd)
;;;; --> T   ;; e->a, a->b, b->c, c->d

(defun reachable (assoc-list from to)
  "Returns t if to is reachable from from in the association list."
  ;; expensive!

;;; SPEED HINT.  You might rewrite this function to be more efficient.
;;; You could try dividing the list into two lists, one consisting of association pairs
;;; known to be reachable from FROM and ones not know to be reachable, then
;;; using the property of transitivity, move pairs from the second list to the first
;;; list, until either you discover it's reachable, or nothing else is moving.

  (dolist (x assoc-list nil)
    (when (and (equalp (car x) from)
	              (or (equalp (cdr x) to)
			     (reachable (remove x assoc-list) (cdr x) to)))
      (return t))))


;;;; Cyclic-assoc-list takes an association list and determines if it
;;;; contains a cycle (two objects can reach each other)
;;;;
;;;; (cyclic-assoc-list '((a . b) (c . d) (b . c) (b . e) (e . a)))
;;;; --> T   ;; a->b, b->e, e->a
;;;;
;;;; (cyclic-assoc-list '((a . a)))
;;;; --> T   ;; a->a

(defun cyclic-assoc-list (assoc-list)
  (dolist (x assoc-list nil)
    (when (reachable assoc-list (cdr x) (car x))
      (return t))))

;;;; Binary-combinations returns all N^2 combinations of T and NIL.
;;;; 
;;;; (binary-combinations 4)
;;;; -->
;;;; ((NIL T NIL T) (T T NIL T)
;;;;  (NIL NIL NIL T) (T NIL NIL T)
;;;;  (NIL T T T) (T T T T)
;;;;  (NIL NIL T T) (T NIL T T)
;;;;  (NIL T NIL NIL) (T T NIL NIL)
;;;;  (NIL NIL NIL NIL) (T NIL NIL NIL)
;;;;  (NIL T T NIL) (T T T NIL)
;;;;  (NIL NIL T NIL) (T NIL T NIL))

(defun binary-combinations (n)
  "Gives all combinations of n t's and nils"
  (let ((bag '(())))
    (dotimes (x n bag)
      (let (bag2)
	(dolist (b bag)
	    (push (cons t b) bag2)
	      (push (cons nil b) bag2))
	(setf bag bag2)))))

(defun before-p (operator1 operator2 plan)
  "Operator1 is ordered before operator2 in plan?"
;;; perhaps you have an existing function which could help here.
  (reachable (plan-orderings plan) operator1 operator2))

(defun link-exists-for-precondition-p (precond operator plan)
  "T if there's a link for the precond for a given operator, else nil.
precond is a predicate."
  (dolist (i (plan-links plan))
    (if (and (equalp (link-precond i) precond) (or (equal (link-from i) operator) (equal (link-to i) operator)))
	(return-from link-exists-for-precondition-p t)))
  nil)


(defun operator-threatens-link-p (operator link plan)
  "T if operator threatens link in plan, because it's not ordered after
or before the link, and it's got an effect which counters the link's effect."
;;; SPEED HINT.  Test the easy tests before the more costly ones.
 ; (format t "Opearator:: ~A Link:: ~A ~%" operator link)
  (if (or (equal operator (link-from link)) (equal operator (link-to link)))
      (return-from operator-threatens-link-p nil))
  (if (before-p operator (link-from link) plan)
      (return-from operator-threatens-link-p nil))
  (if (before-p (link-to link) operator plan)
      (return-from operator-threatens-link-p nil))
  (dolist (effect (operator-effects operator))
    (if (equal (negate effect) (link-precond link))
	(return-from operator-threatens-link-p t)))
  '())
#|
	(progn
	  (dolist (ordering (plan-orderings plan))
	    (if (and (equal operator (car ordering)) (equal (link-to link) (cdr ordering)))
		(return-from operator-threatens-link-p t))))))
  '()) |#

(defun inconsistent-p (plan)
  "Plan orderings are inconsistent"
  (cyclic-assoc-list (plan-orderings plan)))

(defun operator-achieves-effect(operator precondition)
  "given a opeartor and effect checks returns t if operator achieves the effecct"
  (remove-if-not #'(lambda (x) x) (map 'list #'(lambda (x) (if (equal x precondition) x)) (operator-effects operator))))

(defun all-effects(precondition plan)
  "Given a precondition, returns a list of ALL operators presently IN THE PLAN which have
effects which can achieve this precondition."
  (remove-if-not #'(lambda (x) x) (map 'list #'(lambda (x) (if (operator-achieves-effect x precondition) x)) (plan-operators plan))))

(defun all-operators(precondition)
  "Given a precondition, returns all list of ALL operator templates which have
an effect that can achieve this precondition."
  (remove-if-not #'(lambda (x) x) (map 'list #'(lambda (x) (if (operator-achieves-effect x precondition) x)) *operators*)))

(defun open-precond-count(operator plan)
  (let ((count 0))
    (dolist (precond (operator-preconditions operator))
      (if (not (link-exists-for-precondition-p precond operator plan))
	  (setf count (1+ count))))
    count))

(defun pick-operand(plan)
  "Return ONE (operator . precondition) pair in the plan that has not been met yet.
If there is no such pair, return nil"
  ;;;We want to use this opportunity to pick a better one also
  ;;;We don't want to waste too much time, we pick the best among 10 random ones
  (let* ((best-pair '()) (precond-count (mapcar #'cons (mapcar #'(lambda (x) (open-precond-count x plan)) (plan-operators plan)) (plan-operators plan)))
	 (sorted-ops (sort precond-count '< :key 'car)) (iteration-count 0) (best-count 0))
    (dolist (operator sorted-ops)
      (if (not (= (car operator) 0))
	  (progn
	    (if (> iteration-count 10)
		(return-from pick-operand best-pair))
	    (let ((current-op (cdr operator)))
	      (dolist (precond (operator-preconditions current-op))
		(if (and (or (= best-count 0) (< (length (all-operators precond)) best-count)) (not (link-exists-for-precondition-p precond current-op plan)))
		    (progn
		      (setf best-count (length (all-operators precond)))
		      (setf best-pair (cons current-op (list precond)))
		      (setf iteration-count (1+ iteration-count)))))))))
    best-pair))

(defun if-solved-p(plan)
  "Given a plan returns True if the plan is solved
that is we have figured a way to solve all the subgoals"
  (dolist (operator (plan-operators plan))
    (dolist (precond (operator-preconditions operator))
      (if (not (link-exists-for-precondition-p precond operator plan))
	  (return-from if-solved-p nil))))
  t)

(defun select-subgoal(plan current-depth max-depth)
  "For all possible subgoals, recursively calls choose-operator
on those subgoals.  Returns a solved plan, else nil if not solved."
  (loop while( < current-depth max-depth)
     do(progn
	; (format t "Current Depth: ~A MaxDepth: ~A  plan::~A ~%" current-depth max-depth plan)
	 (if (if-solved-p plan)
	     (progn
	       ;(format t "plan solved 1::~A ~%" plan)
	       (return-from select-subgoal plan)))
	 (let ((sub-goal (pick-operand plan)))
	   (setf current-depth(1+ current-depth))
	   (let ((sol (choose-operator sub-goal plan current-depth max-depth)))
	     (if sol
	       (return-from select-subgoal sol))))))
  (if (if-solved-p plan)
      (progn
	;(format t "plan solved 2: ~A ~%" plan)
	plan) nil))

(defun operator-not-added(plan operator)
  (dolist (plan-op (plan-operators plan))
    (if (equalp (operator-name operator) (operator-name plan-op))
	(return-from operator-not-added nil)))
  t)

(defun choose-operator (op-precond-pair plan current-depth max-depth)
  "For a given (operator . precondition) pair, recursively call
hook-up-operator for all possible operators in the plan.  If that
doesn't work, recursively call add operators and call hook-up-operators
on them.  Returns a solved plan, else nil if not solved."
  ;(format t "received op-precond: ~A ~%" op-precond-pair)
  (let* ((operator (first op-precond-pair)) (precond (second op-precond-pair))
	 (new-op-added nil) (plan-ops (all-effects precond plan)) (all-ops (all-operators precond)) (chosen-one nil) (sol nil))
    (dolist (current-op plan-ops)
      (if sol (return-from choose-operator sol))
      (setf chosen-one current-op)
      (setf sol (hook-up-operator chosen-one operator precond plan current-depth max-depth new-op-added)))
    (dolist (current-op all-ops)
      (if sol (return-from choose-operator sol))
      (if (operator-not-added plan current-op)
	  (progn
	    (setf chosen-one (copy-operator-2 current-op))
	    (setf plan (add-operator chosen-one plan))
	    (setf new-op-added chosen-one)
	    (setf sol (hook-up-operator chosen-one operator precond plan current-depth max-depth new-op-added)))))
	  sol))
 

(defun add-operator (operator plan)
  "Given an OPERATOR and a PLAN makes a copy of the plan [the
operator should have already been copied out of its template at this point].
Then adds that copied operator
the copied plan, and hooks up the orderings so that the new operator is
after start and before goal.  Returns the modified copy of the plan."
 ;; (format t "Adding operator ~A ~%" operator)
  (let ((plan-copy (copy-plan-2 plan)))
    (push operator (plan-operators plan-copy))
    (push (cons (plan-start plan) operator) (plan-orderings plan-copy))
    (push (cons operator (plan-goal plan)) (plan-orderings plan-copy))
    plan-copy))

(defun hook-up-operator( from to precondition plan current-depth max-depth new-operator-was-added)
  "Hooks up an operator called FROM, adding the links and orderings to the operator
TO for the given PRECONDITION that FROM achieves for TO.  Then
recursively  calls resolve-threats to fix any problems.  Presumes that
PLAN is a copy that can be modified at will by HOOK-UP-OPERATOR. Returns a solved
plan, else nil if not solved."
  (if (before-p to from plan)
      (return-from hook-up-operator nil))
  (let ((plan-copy (copy-plan-2 plan)) (threats nil) (maybe-threatening-link nil))
    (setf maybe-threatening-link (make-link :from from :to to :precond precondition))
    (pushnew maybe-threatening-link (plan-links plan-copy) :test 'equalp)
    (pushnew (cons from to) (plan-orderings plan-copy) :test 'equalp)
    (setf threats (threats plan new-operator-was-added maybe-threatening-link))
    (resolve-threats plan-copy threats current-depth max-depth)))


(defun threats(plan maybe-threatening-operator maybe-threatening-link)
  (let ((threats '()))
    (if maybe-threatening-operator
	(dolist (link (plan-links plan))
	  (if (operator-threatens-link-p maybe-threatening-operator link plan)
	      (pushnew (cons maybe-threatening-operator link) threats))))
    (dolist (operator (plan-operators plan))
      (if (operator-threatens-link-p operator maybe-threatening-link plan)
	  (pushnew (cons operator maybe-threatening-link) threats :test 'equalp)))
    threats))

(defun all-promotion-demotion-plans (plan threats)
   "Returns plans for each combination of promotions and demotions
of the given threats, except  for the inconsistent plans.  These plans
are copies of the original plan."
   ;;Let me write it down on what has to be done
   ;;I will get a list of operators and links that they threaten
   ;;the only way they can threaten a link is by negating an effect produced by from operator
   ;;We are making an assumption that the threats won't involve inconsistencies?
   ;;So inorder to resolve a threat I need to either promote or demote the operator
   ;;So for each of the threat I can either promote or demote, so if have a n threats
   ;;all I need to do come up with all the combinations of promotions and demotions
   ;;each combination will be a plan by itself. If a any plan turns out to be inconsistent
   ;;I will throw it away and return only the consistent plans
   (let* ((total-threats (length threats)) (resolved-plans '()) (possible-combos (binary-combinations total-threats)))
;;     (format t "Possible combos are ~A Threats:: ~A ~%" possible-combos threats)
     (dolist (current-combo possible-combos)
       (let ((resolved-plan (copy-plan-2 plan)))
	 (mapc #'(lambda (x y) (if x (promote (car y) (cdr y) resolved-plan) (demote (car y) (cdr y) resolved-plan))) current-combo threats)
	 (if (not (inconsistent-p resolved-plan))
	     (setf resolved-plans (append resolved-plans (list resolved-plan))))))
     resolved-plans))

(defun promote (operator link plan)
  "This receives a copy of the plan and tries to promote the operator
with respect to the link given"
(pushnew (cons (link-to link) operator) (plan-orderings plan) :test 'equalp))  

(defun demote (operator link plan)
  "This receives a copy of the plan and tries to demote the operator
with respect to the link given"
  (pushnew (cons operator (link-from link)) (plan-orderings plan) :test 'equalp))

(defun resolve-threats(plan threats current-depth max-depth)
  (let  ((sol nil))
    (if threats
	(let ((solutions (all-promotion-demotion-plans plan threats)))
	  (dolist (solution solutions)
	    (setf sol (select-subgoal solution current-depth max-depth))
	    (if sol (return-from resolve-threats sol))))
	(setf sol (select-subgoal plan current-depth max-depth)))
  sol))

(defparameter *depth-increment* 1
  "The depth to increment in iterative deepening search")

;;; This is used to cache the operators by precond.  You might find this
;;; useful to make your ALL-OPERATORS code much much much faster than the
;;; obvious dorky way to do it.
(defparameter *operators-for-precond* nil
  "Hash table.  Will yield a list of operators which can achieve a given precondition")

(defun build-operators-for-precond ()
  "Buils the hash table"
  (setf *operators-for-precond* (make-hash-table :test #'equalp))
  (dolist (operator *operators*)
    (dolist (effect (operator-effects operator))
      (push operator (gethash effect *operators-for-precond*)))))

(defun do-pop ()
  (let* ((start (make-operator
		  :name 'start
		   :uniq (gensym)
		    :preconditions nil
		     :effects *start-effects*))
	  (goal (make-operator
		 :name 'goal
		 :uniq (gensym)
		 :preconditions *goal-preconditions*
		 :effects nil))
	   (plan (make-plan
		  :operators (list start goal)
		  :orderings (list (cons start goal))
		  :links nil
		  :start start
		  :goal goal))
	    (depth *depth-increment*)
	     solution)
    (build-operators-for-precond)
    ;; Do iterative deepening search on this sucker
    (loop
     (format t "~%Search Depth: ~d" depth)
     (setf solution (select-subgoal plan 0 depth))
     (when solution (return)) ;; break from loop, we're done!
     (incf depth *depth-increment*))
    ;; found the answer if we got here
    (format t "~%Solution Discovered:~%~%")
    solution))


#|
(defparameter *operators*
  (list
   ;; move from table operators
   (make-operator :name 'a-table-to-b
		   :preconditions '((t a-on-table) (t b-clear) (t a-clear))
		    :effects '((nil a-on-table) (nil b-clear) (t a-on-b)))
   (make-operator :name 'b-table-to-a
		   :preconditions '((t b-on-table) (t a-clear) (t b-clear))
		    :effects '((nil b-on-table) (nil a-clear) (t b-on-a)))
   ;; move to table operators
   (make-operator :name 'a-b-to-table
		   :preconditions '((t a-on-b) (t a-clear))
		    :effects '((t a-on-table) (nil a-on-b) (t b-clear)))
   (make-operator :name 'b-a-to-table
		   :preconditions '((t b-on-a) (t b-clear))
		    :effects '((t b-on-table) (nil b-on-a) (t a-clear))))
  "A list of strips operators without their uniq gensyms set yet -- 
doesn't matter really -- but NOT including a goal or start operator")


;;; b is on top of a
(defparameter *start-effects*
  '((t a-on-table) (t b-on-a) (t b-clear)))

;;; a is on top of b
(defparameter *goal-preconditions*
  ;; somewhat redundant, is doable with just ((t a-on-b))
  '((t a-on-b) (t b-on-table) (t a-clear)))

(defparameter  *start*
       ;;;initial start
  (make-operator :name 'start :uniq (gensym) :effects *start-effects*))

(defparameter *goal*
      ;;;Initial goal
  (make-operator :name 'goal :uniq (gensym) :preconditions *goal-preconditions*))

(defparameter *plan*
  ;;;Initial plan that we start with
  (make-plan :operators (list *start* *goal*) :orderings (list (cons *start* *goal*)) :start *start* :goal *goal*))
|#


;;;;;; THREE-BLOCK-WORLD
;;;;;; you have three blocks on the table, A, B, and C.
;;;;;;
;;;;;;
;;;
;;; Why so many operators?  Because we don't have a variable facility.
;;; We can't say MOVE(x,y,z) -- we can only say MOVE(A,TABLE,B).  To
;;; add in a variable facility is a lot more coding, and I figured I'd
;;; save you the hassle of unification.  If you want to give it a shot,
;;; I have written up some unification code which might help you out.
;;; Another consequence of not having a variable facility is that you
;;; can't rely on the least-commitment heuristic of not immediately
;;; binding variables to constants.  For us, we must *immediately*
;;; commit to constants.  That makes our search space much nastier.
;;; C'est la vie!
;;;
 (defparameter *operators*
   (list
    ;; move from table operators
    (make-operator :name 'a-table-to-b
   :preconditions '((t a-on-table) (t b-clear) (t a-clear))
   :effects '((nil a-on-table) (nil b-clear) (t a-on-b)))
    (make-operator :name 'a-table-to-c
   :preconditions '((t a-on-table) (t c-clear) (t a-clear))
   :effects '((nil a-on-table) (nil c-clear) (t a-on-c)))
    (make-operator :name 'b-table-to-a
   :preconditions '((t b-on-table) (t a-clear) (t b-clear))
   :effects '((nil b-on-table) (nil a-clear) (t b-on-a)))
    (make-operator :name 'b-table-to-c
   :preconditions '((t b-on-table) (t c-clear) (t b-clear))
   :effects '((nil b-on-table) (nil c-clear) (t b-on-c)))
    (make-operator :name 'c-table-to-a
   :preconditions '((t c-on-table) (t a-clear) (t c-clear))
   :effects '((nil c-on-table) (nil a-clear) (t c-on-a)))
    (make-operator :name 'c-table-to-b
   :preconditions '((t c-on-table) (t b-clear) (t c-clear))
   :effects '((nil c-on-table) (nil b-clear) (t c-on-b)))
    ;; move to table operators
    (make-operator :name 'a-b-to-table
   :preconditions '((t a-on-b) (t a-clear))
   :effects '((t a-on-table) (nil a-on-b) (t b-clear)))
    (make-operator :name 'a-c-to-table
   :preconditions '((t a-on-c) (t a-clear))
   :effects '((t a-on-table) (nil a-on-c) (t c-clear)))
    (make-operator :name 'b-a-to-table
   :preconditions '((t b-on-a) (t b-clear))
   :effects '((t b-on-table) (nil b-on-a) (t a-clear)))
    (make-operator :name 'b-c-to-table
   :preconditions '((t b-on-c) (t b-clear))
   :effects '((t b-on-table) (nil b-on-c) (t c-clear)))
    (make-operator :name 'c-a-to-table
   :preconditions '((t c-on-a) (t c-clear))
   :effects '((t c-on-table) (nil c-on-a) (t a-clear)))
    (make-operator :name 'c-b-to-table
   :preconditions '((t c-on-b) (t c-clear))
   :effects '((t c-on-table) (nil c-on-b) (t b-clear)))
    ;; block-to-block operators
    (make-operator :name 'a-b-to-c
   :preconditions '((t a-on-b) (t a-clear) (t c-clear))
   :effects '((nil a-on-b) (t a-on-c) (nil c-clear) (t b-clear)))
    (make-operator :name 'a-c-to-b
   :preconditions '((t a-on-c) (t a-clear) (t b-clear))
   :effects '((nil a-on-c) (t a-on-b) (nil b-clear) (t c-clear)))
    (make-operator :name 'b-a-to-c
   :preconditions '((t b-on-a) (t b-clear) (t c-clear))
   :effects '((nil b-on-a) (t b-on-c) (nil c-clear) (t a-clear)))
    (make-operator :name 'b-c-to-a
   :preconditions '((t b-on-c) (t b-clear) (t a-clear))
   :effects '((nil b-on-c) (t b-on-a) (nil a-clear) (t c-clear)))
    (make-operator :name 'c-a-to-b
   :preconditions '((t c-on-a) (t c-clear) (t b-clear))
   :effects '((nil c-on-a) (t c-on-b) (nil b-clear) (t a-clear)))
    (make-operator :name 'c-b-to-a
   :preconditions '((t c-on-b) (t c-clear) (t a-clear))
   :effects '((nil c-on-b) (t c-on-a) (nil a-clear) (t b-clear))))
   "A list of strips operators without their uniq gensyms set yet -- 
 doesn't matter really -- but NOT including a goal or start operator")

 (defparameter *start-effects*
;;   ;; Sussman Anomaly
   '((t a-on-table) (t b-on-table) (t c-on-a) (t b-clear) (t c-clear))
   "A list of predicates which specify the initial state")
#|
 (defparameter *start-effects*
   ;; another simple situation: all on table
   '((t a-on-table) (t a-clear)
    (t b-on-table) (t b-clear)
     (t c-on-table) (t c-clear))) 
|#
 (defparameter *goal-preconditions*
  '((t a-on-b) (t b-on-c) (t c-on-table) (t a-clear)))
