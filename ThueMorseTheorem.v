Require Import Nat.
Require Import Recdef.
Require Import PeanoNat.
Require Import Coq.Arith.Plus.
Require Import Coq.Arith.Div2.
Require Import Even.
Require Import Coq.Bool.Bool.


Lemma negb_eq: (forall a b:bool, negb a = negb b <-> a = b).
Proof.
intros.
split; intros; 
case a in *; case b in *; auto.
Qed.

Theorem even_correct: forall k: nat, (Nat.even(k+k) = true).
Proof.
intros. unfold Nat.even.
induction k. auto.
compute. fold plus. fold Nat.even. rewrite plus_comm.
compute. auto.
Qed.

Hint Resolve even_correct.

Theorem even_correct2: forall k: nat, (Nat.even(S (k+k)) = false).
Proof.
intros. unfold Nat.even.
induction k. auto.
compute. fold plus. fold Nat.even. rewrite plus_comm.
compute. auto.
Qed.

Hint Resolve even_correct2.

Function HasDoubleRepeat(f:nat->bool) (start length:nat): Prop :=
  forall k:nat, (k < length)-> ((f(start + k) = f(start+length+k)) /\ (f(start + k) = f(start+length+length+k))).
Hint Unfold HasDoubleRepeat.

Function HasNoDoubleRepeats(f:nat->bool): Prop  := 
  forall (start length:nat), 
    length = 0 \/ not (HasDoubleRepeat f start length).
Hint Unfold HasNoDoubleRepeats.


Lemma le_plus_one: forall n k:nat, n <= k -> (S n <= S k).
Proof.
auto with v62.
Qed.

Function ThueMorseSequence(n:nat) {measure (fun (x:nat)=> x) n}:= match n with
                  | O => false
                  | S x => xorb (Nat.even x) (ThueMorseSequence(div2(S x)))
               end.
Proof.
unfold lt.

intros.
clear teq.
clear n.
apply le_plus_one.
induction x.
compute.
apply le_n.
compute.
fold div2.
apply le_plus_one.
assert (forall y:nat,((div2 y) <= div2(S y))).
intros.
clear IHx.
clear x.
assert (forall y1: nat, (exists x, (y1 = x + x) \/ (y1 = (S (x + x))))).
intros.
induction y1.
exists 0. auto.
induction IHy1.
case H; intros.
exists  x. right. auto.
exists (S x). left. unfold plus. fold plus.
assert (forall x,x + S x = S (x + x)). auto.
rewrite H1. auto.
assert (exists x : nat, y = x + x \/ y = S (x + x)).
apply H.
assert (forall x,x + S x = S (x + x)). auto.
case H0; intros; clear H0.
case H2; intros; clear H2; rewrite H0;
clear H0.
induction x. auto.
assert (forall x,x + S x = S (x + x)). auto.
unfold plus. fold plus. rewrite H0.
unfold div2 at 1. fold div2. unfold div2 at 2. fold div2.
apply le_plus_one.
unfold div2 in IHx at 2. fold div2 in IHx.
assumption.
induction x. compute. auto.
assert (forall x,x + S x = S (x + x)). auto.
unfold plus. fold plus. rewrite H0.
unfold div2 at 1. fold div2. unfold div2 at 2. fold div2.
apply le_plus_one.
unfold div2 in IHx at 2. fold div2 in IHx.
assumption.
apply Nat.le_trans with (div2 (S x)).
apply H.
assumption.
Qed.
Hint Resolve ThueMorseSequence_equation.
Notation TMS:=ThueMorseSequence.
Notation TMS_eq:=ThueMorseSequence_equation.

Lemma TMS_even: forall k: nat, ThueMorseSequence(k + k) = ThueMorseSequence(k).
Proof. intros.
rewrite ThueMorseSequence_equation.
induction k.
auto.
simpl.
intros.
rewrite plus_comm.
unfold plus. fold plus.
rewrite even_correct2.
rewrite xorb_false_l.
assert (k + k = 2 * k). unfold mult. auto.
rewrite H. rewrite div2_double.
reflexivity.
Qed.

Lemma TMS_odd: forall k: nat, ThueMorseSequence(S (k + k)) = negb(ThueMorseSequence(k)).
Proof.
intros.
rewrite ThueMorseSequence_equation.
induction k.
auto.
simpl.
intros.
rewrite plus_comm.
unfold plus. fold plus.
rewrite even_correct.
rewrite xorb_true_l.
assert (k + k = 2 * k). unfold mult. auto.
rewrite H. rewrite div2_double_plus_one.
reflexivity.
Qed.


Lemma TMS_div2_even: forall n:nat, even n -> TMS(Nat.div2 n) = TMS n.
Proof.
intros.
rewrite <-TMS_even.
assert (n = Nat.div2 n + Nat.div2 n).
assert (forall k: nat, k + k = double k). auto.
rewrite H0.
apply even_double. exact H.
rewrite <-H0.
reflexivity.
Qed.


Lemma TMS_div2_odd: forall n:nat, odd n -> TMS(Nat.div2 n) = negb (TMS n).
Proof.
intros.
apply negb_sym.
rewrite <-TMS_odd.
assert (n = S (Nat.div2 n + Nat.div2 n)).
assert (forall k: nat, k + k = double k). auto.
rewrite H0.
apply odd_double. exact H.
rewrite <-H0.
reflexivity.
Qed.


Lemma TMS_even_S: forall x: nat, even x -> TMS (S x) = negb (TMS x).
Proof.
intros.
rewrite negb_sym with _ (TMS x); auto.
rewrite <- TMS_div2_odd; auto with arith.
rewrite <- TMS_div2_even; auto.
rewrite even_div2; auto.
Qed.


Lemma TMS_even_S_rev: forall x: nat, even x -> TMS x = negb (TMS (S x)).
Proof.
intros.
rewrite <- TMS_div2_odd; auto with arith.
rewrite <- TMS_div2_even; auto.
rewrite even_div2; auto.
Qed.

Theorem ThueMorse: exists f:nat->bool, HasNoDoubleRepeats f.
Proof.
exists ThueMorseSequence.
unfold HasNoDoubleRepeats.
intros.
assert (length = 0 \/ exists l, length = S l). 
induction length. left. auto.
right. case IHlength; intros; exists length; auto.
case H; intros; clear H. left. assumption.
right. induction H0.
unfold not.
rewrite H.
intros.
clear H.
clear length.

generalize H0.
clear H0.
generalize dependent start.
functional induction  TMS x.
intros.
(*case x = 0.*)
assert (TMS (start) = TMS (start + 1) /\ TMS (start) = TMS (start + 1 + 1)).
assert (start + O = start). auto. rewrite <-H at 1 3.
assert (start + 1 = start + 1 + O). auto. rewrite H1 at 1.
assert (start + 1 + 1 = start + 1 + 1 + O). auto. rewrite H2 at 1.
apply (H0 0 ). auto.
case H; clear H; intros.
assert ((exists s:nat, (start = s + s) \/(start = S (s + s)))).
clear H H1 H H0.
induction start.
exists 0. auto.
case IHstart; clear IHstart; intros.
case H; clear H; intros.
exists x. right. rewrite H. reflexivity.
exists ((S x)). left. rewrite H. simpl.
assert (x + S x = S (x + x)). auto.
rewrite H0. reflexivity.
case H2; clear H2; intros.
case H2; clear H2; intros;
clear H0;
rewrite H2 in H; rewrite H2 in H1.
rewrite TMS_even in H.
rewrite plus_comm in H.
simpl in H.
rewrite TMS_odd in H.
case (TMS x) in H;
compute in H;
apply eq_true_false_abs with true; auto.

rewrite TMS_odd in H.
assert (S (x + x) + 1 + 1 = S (S x + S x)).
rewrite plus_comm. simpl. 
rewrite plus_comm. simpl.
apply eq_sym.
rewrite plus_comm. simpl. reflexivity.
rewrite H0 in H1.
rewrite TMS_odd in H1.
rewrite TMS_odd in H1.
assert (S (x + x) + 1 =  ( (S x + S x))).
rewrite plus_comm.
simpl.
assert (S (x + S x) = S (S (x + x))).
auto. auto.
rewrite H3 in H.
rewrite TMS_even in H.
case (TMS (S x)) in *; simpl in H;
apply eq_true_false_abs with (negb (TMS x)); auto.
(*case x <> 0*)
intros.
assert (even x \/ odd x).
apply even_or_odd.
case H; intros; clear H.
(* case x even *)
apply IHb with (div2 start).
assert ((Nat.div2 (S x)) = (Nat.div2 x)).
rewrite <-(even_div2 x); auto.
rewrite H in *. clear H.
unfold HasDoubleRepeat in *.
intros.
assert (Nat.div2 start + k = Nat.div2 (start + 2 * k)).
clear IHb H0 H1 H.
induction k. rewrite plus_comm; simpl. auto.
unfold mul. rewrite plus_comm at 1. simpl.
assert (k + S (k + 0) = S (k + k)).
rewrite plus_comm at 1.
simpl. assert (k + 0 = k). auto.
rewrite H. reflexivity.
rewrite H. clear H. rewrite plus_comm.
rewrite IHk.
rewrite plus_comm with start (S (S (k + k))).
rewrite plus_comm. simpl. rewrite plus_comm with k 0.
simpl. reflexivity.
rewrite H2. clear H2.

assert (Nat.div2 start + S (Nat.div2 x) + k = Nat.div2 (start + S(S(x)) + 2 * k)).
clear IHb H0 H.
induction k. rewrite plus_comm; simpl. 
rewrite plus_comm with _ 0. simpl.
rewrite plus_comm with _ (S (S x)). simpl.
rewrite plus_comm. simpl.
apply eq_S.
assert (exists k: nat, x=k+k).
exists (div2 x). fold (double (Nat.div2 x)).
auto with arith.
case H. intros. clear H.
rewrite H0. clear H0.
clear H1.
induction x0.  auto.
simpl (S x0 + S x0).
rewrite plus_comm with x0 _. simpl.
auto.

unfold mul. rewrite plus_comm at 1. simpl.
assert (k + S (k + 0) = S (k + k)).
rewrite plus_comm at 1.
simpl. assert (k + 0 = k). auto.
rewrite H. reflexivity.
rewrite H. clear H. rewrite plus_comm.
rewrite IHk.
rewrite plus_comm with _ (S (S (k + k))).
simpl.
rewrite plus_comm. simpl. rewrite plus_comm with k 0.
simpl. reflexivity.
rewrite H2. clear H2.

assert (Nat.div2 start + S (Nat.div2 x) + S (Nat.div2 x) + k = div2(start + S (S x) + S (S x) + 2 * k)).
clear IHb H0 H.
induction k. rewrite plus_comm; simpl. 
rewrite plus_comm with _ 0. simpl.
rewrite plus_comm with _ (S (S x)). simpl.
rewrite plus_comm. simpl.
apply eq_S.
assert (exists k: nat, x=k+k).
exists (div2 x). fold (double (Nat.div2 x)).
auto with arith.
case H. intros. clear H.
rewrite H0. clear H0.
clear H1.
induction x0.  auto.
simpl.
rewrite plus_comm with _ 2. simpl.
rewrite plus_comm. simpl.
reflexivity.
simpl (S x0 + S x0).
rewrite plus_comm with x0 _.
simpl.
apply eq_S.
rewrite plus_comm.
rewrite plus_comm with (Nat.div2 start) _.
simpl.
rewrite plus_comm with (x0 + x0) _.
rewrite plus_comm with (start) _.
simpl (Nat.div2 (S (S (S (S (x0 + x0)))) + start + (x0 + x0))).
rewrite plus_comm in IHx0.
rewrite plus_comm with start _ in IHx0.
rewrite plus_comm with (Nat.div2 start) _ in IHx0.
rewrite plus_comm with (x0+x0) _ in IHx0.
simpl.
compute.
compute in IHx0.
rewrite IHx0.
auto.
unfold mul.
simpl.
rewrite plus_comm with _ 0. simpl.
rewrite plus_comm with k _. simpl.
rewrite plus_comm with _ (S k). simpl.
rewrite plus_comm with k _.
rewrite IHk.
rewrite plus_comm with _ (S (S (k + k))). simpl (Nat.div2 (S (S (k + k)) + (start + S (S x) + S (S x)))).
simpl. rewrite plus_comm with _ 0. simpl.
rewrite plus_comm with _ (k + k). reflexivity.
rewrite H2. clear H2.
assert (even start \/ odd start).
apply even_or_odd.
case H2; intros;clear H2.

clear IHb.
assert (even (start + 2 * k)).
apply even_even_plus. auto.
apply even_mult_l. auto with arith.
rewrite TMS_div2_even; auto.
clear H2.
assert (even (start + S (S x) + 2 * k)).
apply even_even_plus. apply even_even_plus; auto with arith.
apply even_mult_l. auto with arith.
rewrite TMS_div2_even; auto.
clear H2.
assert (even (start + S (S x) + S (S x) + 2 * k)).
apply even_even_plus; auto with arith.
rewrite TMS_div2_even; auto.
clear H2.
apply H0.
rewrite even_double.
unfold Nat.double.
unfold mul. simpl (Nat.div2 (S (S x))).
rewrite plus_comm with _ 0. simpl (0 + k).
apply plus_lt_le_compat; auto.
unfold lt in H.
apply Nat.le_trans with (S k).
auto.
auto.
auto with arith.


clear IHb.
assert (odd (start + 2 * k)).
apply odd_plus_l. auto.
apply even_mult_l. auto with arith.
rewrite TMS_div2_odd; auto.
clear H2.
assert (odd (start + S (S x) + 2 * k)).
apply odd_plus_l. apply odd_plus_l; auto with arith.
apply even_mult_l. auto with arith.
rewrite TMS_div2_odd; auto.
clear H2.
assert (odd (start + S (S x) + S (S x) + 2 * k)).
apply odd_plus_l; auto with arith.
rewrite TMS_div2_odd; auto.
clear H2.

rewrite negb_eq.
rewrite negb_eq.
apply H0.
rewrite even_double.
unfold Nat.double.
unfold mul. simpl (Nat.div2 (S (S x))).
rewrite plus_comm with _ 0. simpl (0 + k).
apply plus_lt_le_compat; auto.
unfold lt in H.
apply Nat.le_trans with (S k).
auto.
auto.
auto with arith.

(* case odd x *)
clear IHb.
assert (even start \/ odd start).
apply even_or_odd.
case H; intros; clear H.
(* case even start *)
pose (st:=start).
assert (forall k : nat,
     k < S (S x) ->
     TMS (st + k) = TMS (st + S (S x) + k)).
apply H0.
clear H0.
assert (TMS (st + 0) = TMS ((st + S (S x)) + 0)).
apply H.
auto with arith.
assert (TMS (st + 2) = TMS (st + 0)).
assert (TMS (st + 2) = TMS ((st + S (S x)) + 2)).
apply H.
unfold lt.
apply le_plus_one.
apply le_plus_one.
apply odd_ind; auto.
intros. induction n; auto with arith.
rewrite H3.
rewrite plus_comm.
simpl.
rewrite TMS_even_S; auto with arith.
rewrite TMS_even_S_rev with (st + 0); auto with arith.
rewrite negb_eq.
assert (TMS (st + 1) = TMS (st + S (S x) + 1)).
apply H.
apply le_plus_one.
apply le_plus_one; auto.
intros. induction x; auto with arith.
rewrite plus_comm in H4.
simpl in H4.
rewrite plus_comm with _ 0. simpl.
rewrite H4.
rewrite plus_comm with _ 1. simpl.
reflexivity.
assert (x <= 2 \/ 2 < x) as tmp.
clear H1 H2 H H0 H3.
induction x.
auto with arith.
clear IHx.
induction x.
auto with arith.
clear IHx.
induction x.
auto with arith.
clear IHx.
right. auto with arith.
induction tmp.
(* case x < 3 => len < 5*)
case x in *.
inversion H1.
case x in *.
clear H4 H1.
rewrite  plus_comm with _ 0 in *.
rewrite  plus_comm with _ 0 in *.
simpl in *.
rewrite H0 in H3.
rewrite TMS_even_S_rev in H3; auto with arith.
rewrite plus_comm with _ 3 in H3.
rewrite plus_comm with _ 2 in H3.
simpl in H3.
case (TMS (S (S (S st)))) in *; simpl in H3;
 apply eq_true_false_abs with true; auto.
case x in *.
inversion H1. inversion H6. inversion H8.
inversion H4. inversion H6. inversion H8.
assert (TMS (st + 4) = TMS (st + 0)).
rewrite H; auto with arith.
rewrite plus_comm.
simpl.
rewrite <-negb_eq.
rewrite <-TMS_even_S_rev; auto with arith.
assert ((S (S (S (st + S (S x))))) = st + S (S x) + 3).
rewrite plus_comm with _ 3.
auto with arith.
rewrite H5. clear H5.
rewrite <- H; auto with arith.
rewrite plus_comm. simpl.
apply negb_sym.
rewrite <-TMS_even_S_rev; auto with arith.
rewrite <-H3. rewrite plus_comm. auto.
rewrite plus_comm. simpl.
apply even_S.
apply odd_S.
auto with arith.

rewrite <-TMS_div2_even in H3; auto with arith.
rewrite <-TMS_div2_even in H5; auto with arith.
rewrite <-TMS_div2_even with (st + 0) in H3; auto with arith.
rewrite <-TMS_div2_even with (st + 0) in H5; auto with arith.
rewrite plus_comm in *. simpl in *.
rewrite plus_comm with _ 0 in *. simpl in *.
assert (even (Nat.div2 st) \/ odd (Nat.div2 st)). apply even_or_odd.
induction H6.
rewrite TMS_even_S in H3; auto with arith.
case (TMS (Nat.div2 st)) in *; compute in H3;
apply eq_true_false_abs with false; auto.
rewrite <- H3 in H5.
rewrite TMS_even_S in H5; auto with arith.
case (TMS (S (Nat.div2 st))) in *; compute in H5;
apply eq_true_false_abs with false; auto.

(* case odd start is similar to case even start *)

pose (st:=start + (S (S x))).
assert (forall k : nat,
     k < S (S x) ->
     TMS (st + k) = TMS (st + S (S x) + k)).
unfold HasDoubleRepeat in H0.
assert (forall k : nat,
     k < S (S x) ->
     TMS (start + k) = TMS (st + k)).
apply H0.
intros.
rewrite <- H.
apply H0.
assumption.
assumption.
clear H0.

(* after this block code for even start and odd start is the same *)
rename H2 into tmp.
assert (even st) as H2.
apply odd_even_plus; auto with arith.
assert (TMS (st + 0) = TMS ((st + S (S x)) + 0)).
apply H.
auto with arith.
clear tmp.


assert (TMS (st + 2) = TMS (st + 0)).
assert (TMS (st + 2) = TMS ((st + S (S x)) + 2)).
apply H.
unfold lt.
apply le_plus_one.
apply le_plus_one.
apply odd_ind; auto.
intros. induction n; auto with arith.
rewrite H3.
rewrite plus_comm.
simpl.
rewrite TMS_even_S; auto with arith.
rewrite TMS_even_S_rev with (st + 0); auto with arith.
rewrite negb_eq.
assert (TMS (st + 1) = TMS (st + S (S x) + 1)).
apply H.
apply le_plus_one.
apply le_plus_one; auto.
intros. induction x; auto with arith.
rewrite plus_comm in H4.
simpl in H4.
rewrite plus_comm with _ 0. simpl.
rewrite H4.
rewrite plus_comm with _ 1. simpl.
reflexivity.
assert (x <= 2 \/ 2 < x) as tmp.
clear H1 H2 H H0 H3.
induction x.
auto with arith.
clear IHx.
induction x.
auto with arith.
clear IHx.
induction x.
auto with arith.
clear IHx.
right. auto with arith.
induction tmp.
(* case x < 3 => len < 5*)
case x in *.
inversion H1.
case x in *.
clear H4 H1.
rewrite  plus_comm with _ 0 in *.
rewrite  plus_comm with _ 0 in *.
simpl in *.
rewrite H0 in H3.
rewrite TMS_even_S_rev in H3; auto with arith.
rewrite plus_comm with _ 3 in H3.
rewrite plus_comm with _ 2 in H3.
simpl in H3.
case (TMS (S (S (S st)))) in *; simpl in H3;
 apply eq_true_false_abs with true; auto.
case x in *.
inversion H1. inversion H6. inversion H8.
inversion H4. inversion H6. inversion H8.
assert (TMS (st + 4) = TMS (st + 0)).
rewrite H; auto with arith.
rewrite plus_comm.
simpl.
rewrite <-negb_eq.
rewrite <-TMS_even_S_rev; auto with arith.
assert ((S (S (S (st + S (S x))))) = st + S (S x) + 3).
rewrite plus_comm with _ 3.
auto with arith.
rewrite H5. clear H5.
rewrite <- H; auto with arith.
rewrite plus_comm. simpl.
apply negb_sym.
rewrite <-TMS_even_S_rev; auto with arith.
rewrite <-H3. rewrite plus_comm. auto.
rewrite plus_comm. simpl.
apply even_S.
apply odd_S.
auto with arith.

rewrite <-TMS_div2_even in H3; auto with arith.
rewrite <-TMS_div2_even in H5; auto with arith.
rewrite <-TMS_div2_even with (st + 0) in H3; auto with arith.
rewrite <-TMS_div2_even with (st + 0) in H5; auto with arith.
rewrite plus_comm in *. simpl in *.
rewrite plus_comm with _ 0 in *. simpl in *.
assert (even (Nat.div2 st) \/ odd (Nat.div2 st)). apply even_or_odd.
induction H6.
rewrite TMS_even_S in H3; auto with arith.
case (TMS (Nat.div2 st)) in *; compute in H3;
apply eq_true_false_abs with false; auto.
rewrite <- H3 in H5.
rewrite TMS_even_S in H5; auto with arith.
case (TMS (S (Nat.div2 st))) in *; compute in H5;
apply eq_true_false_abs with false; auto.


Qed.
