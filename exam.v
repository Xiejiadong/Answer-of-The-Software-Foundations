(* Final Exam (Paper A) --- January 4, 2021 *)
Require Import Nat.
Require Import List.

Notation "[ ]" := nil. 
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Definition admit {T: Type} : T.  Admitted.

(* 1. Prove the following fact about natural numbers. 
Hint: You may search and use some properties about the plus function 
in the standard library of Coq. *)

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - rewrite <- plus_n_O.  reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Lemma mul_3_r : forall n : nat, n * 3 = n + n + n.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn.
    rewrite (plus_comm (n + S n) (S n)). simpl.
    rewrite (plus_comm n (S n)). simpl.
    rewrite (plus_comm n (S(n + n))). simpl.
    reflexivity.
Qed.

(* 2. Complete the following definition so that (div2021 n) returns true 
iff n is divisible by 2021. 
Hint: You may find the leb function useful. *)

Fixpoint div2021 (n : nat ) : bool :=
  match n with
  | O => true
  | S n' => 
    match (leb n 2020) with
    | true => false
    | false => div2021 (n' -2020)
    end
  end.

Example div2021_test1: div2021 4042 = true.
Proof. reflexivity. Qed.

Example div2021_test2: div2021 2027 = false.
Proof. reflexivity. Qed.


(* 3. Define a function createList such that (createList n) returns 
a list of numbers in the form: [n;(n-1);...;2;1;2;...;(n-1);n], for any n > 0. *)

Fixpoint createList1 (n : nat) : list nat :=
  match n with
  | 0 => []
  | 1 => []
  | S n' => S n' :: (createList1 n')
  end.

Definition createList (n : nat) : list nat :=
  match n with
  | 0 => []
  | 1 => [1]
  | n => (createList1 n) ++ [1] ++ (rev (createList1 n))
  end.

Example createList_test : createList 6 = [6;5;4;3;2;1;2;3;4;5;6].
Proof. simpl. reflexivity. Qed.



(* 4. Let oddn and evenn be the predicates that test whether a given number
is odd or even. Show that the sum of an odd number with an even number is odd. *)

Inductive oddn : nat -> Prop :=
 | odd1 : oddn 1
 | odd2 : forall n, oddn n -> oddn (S (S n)).

Inductive evenn : nat -> Prop :=
 | even1 : evenn 0
 | even2 : forall n, evenn n -> evenn (S (S n)).


Theorem odd_add1: forall n, oddn n -> evenn ( S n ).
Proof.
  intros.
  induction H.
  - apply even2. apply even1.
  - apply even2. apply IHoddn.
Qed.

Theorem odd_add2: forall n, evenn n -> oddn ( S n ).
Proof.
  intros.
  induction H.
  - apply odd1.
  - apply odd2. apply IHevenn.
Qed.

Theorem odd_add3: forall n m, evenn n -> evenn m -> evenn (n + m).
Proof.
  intros.
  induction H.
  - apply H0.
  - simpl. apply even2. apply IHevenn.
Qed.

Theorem odd_add : forall n m, oddn n -> evenn m -> oddn (n + m).
Proof.
  intros.
  assert(H1: evenn (S n + m )).
  { apply (odd_add3 (S n) m). apply odd_add1. apply H. apply H0. }
  simpl in H1. inversion H1. apply odd_add2. apply H3.
Qed.



(* 5. Write a function (partition):

      partition : list nat -> list (list nat )

   which partitions a list into a list of 3 sublists. The first sublist
   contains all even numbers in the original list. The second sublist 
   contains all odd numbers divisible by 5 in the original list. The last 
   sublist contains all other elements. The order of elements in the
   three sublists should be the same as their order in the original list. 

   Hint: You may use the Coq function (filter).
*)

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Fixpoint div5 (n : nat ) : bool :=
  match n with
  | O => true
  | S n' => 
    match (leb n 4) with
    | true => false
    | false => div5 (n' -4)
    end
  end.

Definition partition (l : list nat) : list (list nat) :=
  [filter evenb l;
   filter (fun n => andb (negb (evenb n)) (div5 n)) l;
   filter (fun n => andb (negb (evenb n)) (negb (div5 n))) l].

Example partition_test: partition [1;2;3;9;4;5;6;15;8] = [[2;4;6;8]; [5;15]; [1;3;9]].
Proof. reflexivity. Qed.

(* 6. Prove the following fact about excluded middle. *)

(*我们在 Logic.v 中了解到，(forall P, P \/ ~P) 是无法被 Coq 所证明的
而这道题目中，我们发现前提和结论是相互独立的。而且前提必为 True，所以我们必须要证明
结论是 True 的，这里我们引入一条公理来帮助证明*)

Axiom double_negation_elimination : forall P:Prop,
  ~~P -> P.

Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  unfold not. intros P H.
  apply H.
  right.
  intros.
  apply H.
  left.
  apply H0.
Qed.

Theorem excluded_middle : 
  (forall P Q : Prop, (P -> Q) -> (~P \/ Q)) -> (forall P, P \/ ~P).
Proof.
  intros.
  apply (double_negation_elimination (P \/ ~ P)).
  apply excluded_middle_irrefutable.
Qed.
  
  



(* 7. Let a sequence of numbers F(n) be given as follows.
   F(0) = 0
   F(n) = F(n-1) + 2 * n   for n > 0.

Define the function Seq such that (Seq n) returns the sequence

[0; F(1); 2; F(3); 4; F(5); ... ; 2n; F(2n + 1)].
*)

Fixpoint F (n : nat) :nat :=
  match n with 
  |0 => 0
  |S n' => (F n') + (2 * n)
  end.


Fixpoint Seq (n: nat) : list nat :=
  match n with
  |0 => [0] ++ [(F 1)]
  |S n' => (Seq n') ++ [n * 2] ++ [(F ((n *2)+1))]
  end.

Example Seq_test :  Seq 5 = [0; 2; 2; 12; 4; 30; 6; 56; 8; 90; 10; 132].
Proof. reflexivity. Qed.



(* 8. Consider the following type:

Inductive btree : Set :=
 | leaf : nat -> btree 
 | node : nat -> btree -> btree -> btree.

Define a function taking as argument a tree t: btree and returning 
the sum of all numbers occurring in the tree. *)

Inductive btree : Set :=
 | leaf : nat -> btree 
 | node : nat -> btree -> btree -> btree.

Fixpoint sum (t: btree) : nat :=
  match t with
  |leaf n => n
  |node n b1 b2 => n + (sum b1) + (sum b2)
  end.

Example bt_test : sum (node 5 (node 1 (leaf 0) (node 3 (leaf 2) (leaf 4))) 
                              (node 9 (node 7 (leaf 6) (leaf 8)) (leaf 10))) 
                  = 55.
Proof. reflexivity. Qed.


(* 9. Write in Coq a function that rotates a list. Namely, the call to
(rotate l) returns a new list that is the same as l except that the last 
element of l instead appears as the first element of the new list. *)

Fixpoint rotate_hd (l : list nat) : list nat :=
  match l with
  | nil => nil
  | h :: nil => nil
  | h :: t => h :: (rotate_hd t)
  end.

Fixpoint rotate_tl (l : list nat) : list nat :=
  match l with
  | nil => nil
  | h :: nil => [h]
  | h :: t => rotate_tl t
  end.

Definition rotate (l : list nat) : list nat :=
  (rotate_tl l) ++ (rotate_hd l).

Example rotate_test : rotate [1;2;3;4;5] = [5;1;2;3;4].
Proof. reflexivity. Qed.



(* 10. The following definitions specify the abstract syntax of
    some arithmetic expressions and an evaluation function. *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

(* Suppose we define a function that takes an arithmetic expression 
   and slightly simplifies it, changing every occurrence of [e + 0]
   and [e - 0] into just [e], and [e * 1] into [e]. *)

Fixpoint optimize (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus e1 (ANum 0) => optimize e1
  | AMinus e1 (ANum 0) => optimize e1
  | AMult e1 (ANum 1) => optimize e1
  | APlus  e1 e2 => APlus  (optimize e1) (optimize e2)
  | AMinus e1 e2 => AMinus (optimize e1) (optimize e2)
  | AMult  e1 e2 => AMult  (optimize e1) (optimize e2)
  end.


(* Prove the following theorem that states the correctness of the 
optimization with respect to the evaluation of arithmetic expressions. *)

Theorem optimize_mult1_sound1: forall n,
  n + 0 = n.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem optimize_mult1_sound2: forall n,
  n - 0 = n.
Proof.
  intros.
  destruct n.
  - reflexivity.
  - simpl. reflexivity.
Qed.

Theorem optimize_mult1_sound3: forall n,
  n * 1 = n.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem optimize_mult1_sound: forall a,
  aeval (optimize a) = aeval a.
Proof.
  intros a.
  induction a.
  - (* ANum *) reflexivity.
  - (* APlus *)  destruct a2 eqn:Ea1.
    + destruct n eqn:En.
      * simpl. rewrite optimize_mult1_sound1. apply IHa1.
      * simpl. rewrite IHa1. reflexivity.
    + simpl. simpl in IHa2. rewrite IHa2.
      rewrite IHa1. reflexivity.
    + simpl. simpl in IHa2. rewrite IHa2.
      rewrite IHa1. reflexivity.
    + simpl. simpl in IHa2. rewrite IHa2.
      rewrite IHa1. reflexivity.
  - (* AMinus *) destruct a2 eqn:Ea1.
    + destruct n eqn:En.
      * simpl. rewrite optimize_mult1_sound2. apply IHa1.
      * simpl. rewrite IHa1. reflexivity.
    + simpl. simpl in IHa2. rewrite IHa2.
      rewrite IHa1. reflexivity.
    + simpl. simpl in IHa2. rewrite IHa2.
      rewrite IHa1. reflexivity.
    + simpl. simpl in IHa2. rewrite IHa2.
      rewrite IHa1. reflexivity.
  - (* AMult *) destruct a2 eqn:Ea1.
    + (* a1 = ANum n *) destruct (n =? 1) eqn:En.
      * simpl. admit. (*有了 eqn, match n = 1 不知道怎么使得 En 匹配上可以 rewrite*)
      * simpl. admit. (*有了 eqn, match n = _ 不知道怎么使得 En 匹配上可以 rewrite*)
    + simpl. simpl in IHa2. rewrite IHa2.
      rewrite IHa1. reflexivity.
    + simpl. simpl in IHa2. rewrite IHa2.
      rewrite IHa1. reflexivity.
    + simpl. simpl in IHa2. rewrite IHa2.
      rewrite IHa1. reflexivity.
Admitted.
 
