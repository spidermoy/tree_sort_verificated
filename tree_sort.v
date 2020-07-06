(*
  Author: Cenobio Moisés Vázquez Reyes

  This module is a formal verification of the sorting algorithm 'tree sort'.

*)

Require Import List.
Require Import Coq.Unicode.Utf8_core.

(* Definition: x ∊ L, where 'L' is a simple list. *)
Fixpoint in_list (x:nat) (l:list nat) :=
  match l with
  | nil   => False
  | y::ys => x = y \/ in_list x ys
  end.


(* Sort list definition. *)
Fixpoint list_is_sort (l:list nat) :=
  match l with
  | nil   => True
  | x::xs => (∀ y, in_list y xs -> x <= y) /\ list_is_sort xs
  end.


(* Definition: Binary tree. *)
Inductive btree :=
  | Void : btree
  | N    : nat->btree->btree->btree.


(* Definition: x ∊ T, where 'T' is a binary tree. *)
Fixpoint in_tree n t :=
  match t with
  | Void      => False
  | N m t1 t2 => n = m \/ in_tree n t1 \/ in_tree n t2
  end.


(* Definition: Binary search tree. *)
Fixpoint bstree t :=
  match t with
  | Void    => True
  | N n l r => (∀ m, in_tree m l -> m < n)  /\
               (∀ m, in_tree m r -> n <= m) /\
                bstree l /\ bstree r
  end.


(* Definition: In-order tree traversal. *)
Fixpoint in_order (t:btree) :=
  match t with
  | Void    => nil
  | N n l r => in_order l ++ (n::in_order r)
  end.


Definition leaf n := N n Void Void.


(* Definition: Insert a number in a BST. *)
Fixpoint insert_BST x t :=
  match t with
  | Void    => leaf x
  | N n l r => match Nat.ltb x n with
               | true  => (N n (insert_BST x l) r)
               | false => (N n l (insert_BST x r))
               end
  end.


(* Definition: insert a list in a BST. *)
Fixpoint insert_list_in_BST l t :=
  match l with
  | nil   => t
  | x::xs => insert_list_in_BST xs (insert_BST x t)
  end.


(* List to BST. *)
Definition list_to_BST l := insert_list_in_BST l Void.

Proposition in_insertBST : ∀ m x t, in_tree m (insert_BST x t) ->
                                                         (m = x \/ in_tree m t).
Proof.
intros.
induction t.
(* base case *)
simpl in H; intuition.
(* inductive case *)
simpl in H.
case (Nat.ltb x n) in H.
destruct H.
right.
simpl.
left; trivial.
destruct H.
apply IHt1 in H.
destruct H.
left; trivial.
right.
simpl.
right; left; trivial.
right.
simpl.
right; right; trivial.
destruct H.
right.
simpl.
left; trivial.
destruct H.
right.
simpl.
right; left; trivial.
apply IHt2 in H.
destruct H.
left; trivial.
right.
simpl.
right; right; trivial.
Qed.


Lemma insertBST : ∀ x t, bstree t -> bstree (insert_BST x t).
Proof.
(* base case *)
intros.
induction t.
simpl; intuition.
(* inductive case *)
simpl.
(* case: x < n = true *)
destruct (Bool.bool_dec (Nat.ltb x n) true).
rewrite e.
simpl.
split.
intros.
assert (∀ x n, Nat.ltb x n = true -> x < n).
  intro.
  induction x0.
  destruct n0.
  intros.
  inversion H1.
  intros.
  apply Lt.neq_0_lt.
  intuition.
  inversion H2.
  destruct n0.
  intros.
  inversion H1.
  intros.
  simpl in H1.
  apply Lt.lt_n_S.
  apply IHx0; trivial.
apply in_insertBST in H0.
destruct H0.
rewrite <- H0 in e.
apply H1 in e.
trivial.
apply H.
trivial.
split.
intros.
apply H; trivial.
split.
apply IHt1; apply H.
apply H.
(* x < n = false *)
apply Bool.not_true_is_false in n0.
rewrite n0.
simpl.
split.
intros.
inversion H.
intuition.
split.
intros.
apply in_insertBST in H0.
destruct H0.
apply PeanoNat.Nat.ltb_ge in n0.
rewrite H0; trivial.
inversion H.
apply H2; trivial.
split.
apply H.
apply IHt2.
apply H.
Qed.


Lemma insertListToBST : ∀ l t, bstree t -> bstree (insert_list_in_BST l t).
Proof.
induction l.
(* base case *)
intros.
simpl; trivial.
(* inductive case *)
intros.
simpl.
apply IHl.
apply insertBST; trivial.
Qed.


Lemma tailSort : ∀ l, list_is_sort l -> list_is_sort (tail l).
Proof.
induction l.
(* base case *)
intros.
trivial.
(* inductive case *)
intros.
simpl.
simpl in H.
apply H.
Qed.


Lemma InAppend : ∀ x l1 l2, in_list x (l1 ++ l2) -> (in_list x l1 \/ in_list x l2).
Proof.
intros.
induction l1.
(* base case *)
right.
exact H.
(* inductive case *)
simpl in H.
destruct H.
left.
simpl.
left; trivial.
apply IHl1 in H.
destruct H.
left.
simpl.
right; trivial.
right; trivial.
Qed.


Lemma sortAppend : ∀ l1 l2 n, list_is_sort l1 ->
                              list_is_sort (n::l2) ->
                              (∀ m, in_list m l1 -> m <= n) ->
                              list_is_sort (l1 ++ (n::l2)).
Proof.
intro.
induction l1.
(* base case *)
intros.
simpl.
split.
intros.
apply H0.
trivial.
apply tailSort in H0; trivial.
(* inductive case *)
intros.
split.
intros.
apply InAppend in H2.
destruct H2.
apply H; trivial.
inversion H.
inversion H0.
destruct H2.
rewrite H2.
apply H1.
left; trivial.
apply (PeanoNat.Nat.le_trans a n y).
apply H1.
left; trivial.
apply H5; intuition.
apply IHl1.
apply H.
exact H0.
intros.
apply H1.
right; trivial.
Qed.


Lemma InTree_iff_InList : ∀ x t, in_tree x t <-> in_list x (in_order t).
Proof.
(* -> *)
split.
induction t.
(* base case *)
intros.
inversion H.
(* inductive case *)
intros.
simpl.
assert (∀ x l1 l2, (in_list x l1 \/ in_list x l2) -> in_list x (l1 ++ l2)).
  intros.
  induction l1.
  simpl.
  destruct H0.
  inversion H0.
  trivial.
  simpl.
  destruct H0.
  simpl in H0.
  destruct H0.
  left.
  trivial.
  right.
  apply IHl1.
  left.
  trivial.
  right.
  apply IHl1.
  right.
  trivial.
apply (H0 x (in_order t1) (n :: in_order t2)).
destruct H.
right.
simpl.
left.
trivial.
destruct H.
left.
apply IHt1.
trivial.
right.
simpl.
right.
apply IHt2.
trivial.
(* <- *)
induction t.
(* base case *)
intros.
simpl in H.
exfalso;trivial.
(* inductive case *)
intros.
simpl.
simpl in H.
apply InAppend in H.
destruct H.
right; left.
apply IHt1; trivial.
simpl in H.
destruct H.
left; trivial.
right; right.
apply IHt2; trivial.
Qed.


Lemma inOrderSort : ∀ t, bstree t -> list_is_sort (in_order t).
Proof.
induction t.
(* base case *)
intros.
trivial.
(* inductive case *)
intros.
simpl.
apply sortAppend.
apply IHt1.
apply H.
simpl list_is_sort.
split.
intros.
apply InTree_iff_InList in H0.
apply H.
trivial.
apply IHt2.
apply H.
intros.
apply InTree_iff_InList in H0.
inversion H.
apply H1 in H0.
apply PeanoNat.Nat.lt_le_incl in H0.
exact H0.
Qed.


Definition tree_sort l := in_order (list_to_BST l).


Theorem treeSort_correct : ∀ l, list_is_sort (tree_sort l).
Proof.
intros.
unfold tree_sort.
apply inOrderSort.
apply insertListToBST.
simpl; trivial.
Qed.

