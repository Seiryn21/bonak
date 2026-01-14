From Stdlib Require Import Arith Program.Equality.
From Bonak Require Import νSet SigT HSet Notation LeSProp.

Section Category.
Variable arity : HSet.

Definition add_succ_r (n m : nat) : n + m.+1 = (n + m).+1.
Proof.
  induction n.
  + reflexivity.
  + simpl. now rewrite IHn.
Defined. 

Ltac le_contra Hq :=
  exfalso; clear -Hq; repeat apply leR_lower_both in Hq;
  now apply leR_O_contra in Hq.

Ltac find_raise q :=
  match q with
  | ?q.+1 => find_raise q
  | 0 => constr:(@None nat)
  | _ => constr:(Some q)
  end.

Ltac invert_le Hpq :=
  match type of Hpq with
  | ?p.+1 <= ?q =>
     match find_raise q with
     | Some ?c => destruct c; [le_contra Hpq|]
     | None =>
       match find_raise p with
       | Some ?c => destruct c; [|le_contra Hpq]
       | None => le_contra Hpq
       end
     end
  end.

Lemma leR_m {n} (m : nat) : leR m (m + n).
  induction m.
  + exact leR_O.
  + exact (leR_raise_both IHm).
Qed.

Lemma leR_raise_k {n m} (k : nat) (Hnm : leR n m): leR n (m + k).
  induction k.
  + rewrite Nat.add_0_r. exact Hnm.
  + rewrite Nat.add_succ_r. 
    exact (leR_up IHk).
Qed.

Inductive Hom : nat -> nat -> Type := 
| base : Hom 0 0
| nil_cons : forall {n p}, Hom p n -> Hom p.+1 n.+1
| ari_cons : forall {n p} (a : arity), Hom p n -> Hom p n.+1.

Arguments nil_cons {n p} _.
Arguments ari_cons {n p} _ _.

Ltac Hom_destruct f :=
  match type of f with
  | Hom ?p ?n =>
    pattern f;
    match goal with
    | |- context P [ f ] =>
      let H0 := fresh "H" in
      let H1 := fresh "H" in
      refine (
        match f as f' in Hom p' n'
        return forall (H0 : p' = p) (H1 : n' = n), 
          ltac:(let t := context P
            [rew [Hom p] H1 in 
            rew [fun x => Hom x n'] H0 in f'] in exact t)
        with
        | base => fun H0 H1 => _
        | nil_cons f => fun H0 H1 => _
        | ari_cons a f => fun H0 H1 => _
        end eq_refl eq_refl
      );
      destruct H0;
      match type of H1 with
      | 0 = ?x.+1 => discriminate H1
      | ?x.+1 = ?y.+1 => let H2 := fresh "H" in
                         inversion H1 as [H2];
                         destruct H2;
                         rewrite (UIP_nat _ _ H1 eq_refl);
                         clear H1
      | _ => destruct H1
      end;
      unfold eq_rect
    end
  end.

Fixpoint hom_ineq {p n : nat} (f : Hom p n) : p <= n.
Proof.
  destruct f.
  + exact sI.
  + exact (hom_ineq _ _ f).
  + exact (↑ (hom_ineq _ _ f)).
Defined.

Fixpoint id (n : nat) : Hom n n :=
 match n with
 | O => base
 | S n => nil_cons (id n)
 end.

Definition id_suc {n} : id n.+1 = nil_cons (id n) := eq_refl. 

Fixpoint restr (a : arity) (p n : nat) (Hp : p <= n) : Hom n n.+1.
Proof.
  induction p.
  + exact (ari_cons a (id n)).
  + invert_le Hp.
    exact (nil_cons (restr a p n (⇓ Hp))).
Defined.

Definition restr_0 (a : arity) (n : nat) :
  restr a 0 n (leR_O) = ari_cons a (id n) := eq_refl.

Definition restr_suc (a : arity) (p n : nat) (Hp : p.+1 <= n.+1) :
  restr a p.+1 n.+1 Hp = nil_cons (restr a p n (⇓ Hp)) := eq_refl.

Fixpoint compose {n p q : nat} (g : Hom q n) (f : Hom p q) : Hom p n.
Proof.
  destruct g as [|q n g'|q n a g'].
  + exact f.
  + inversion f as [|n' p' f' |n' p' a f'].
    - exact (nil_cons (compose _ _ _ g' f')).
    - exact (ari_cons a (compose _ _ _ g' f')).
  + exact (ari_cons a (compose _ _ _ g' f)). 
Defined.

Definition compose_nil_nil {n p q} (g : Hom q n) (f : Hom p q) :
  compose (nil_cons g) (nil_cons f) = nil_cons (compose g f) := eq_refl.

Definition compose_nil_ari {n p q a} (g : Hom q n) (f : Hom p q) :
  compose (nil_cons g) (ari_cons a f) = ari_cons a (compose g f) := eq_refl.

Definition compose_ari {n p q a} (g : Hom q n) (f : Hom p q) :
  compose (ari_cons a g) f = ari_cons a (compose g f) := eq_refl.

Lemma compose_idl {n p} (f : Hom n p) : compose (id p) f = f.
Proof.
  induction f.
  + reflexivity.
  + rewrite id_suc, compose_nil_nil.
    now rewrite IHf.
  + rewrite id_suc, compose_nil_ari.
    now rewrite IHf.
Qed.

Lemma compose_idr {n p} (f : Hom n p) : compose f (id n) = f.
Proof.
  induction f.
  + reflexivity.
  + rewrite id_suc, compose_nil_nil.
    now rewrite IHf.
  + rewrite compose_ari.
    now rewrite IHf.
Qed.

Lemma compose_assoc {n p q r} (f : Hom r n) (g : Hom q r) (h : Hom p q) :
  compose (compose f g) h = compose f (compose g h).
Proof.
  revert p q g h.
  induction f as [|n r| n r]; intros p q g h.
  + reflexivity.
  + Hom_destruct g.
    - Hom_destruct h.
      * repeat rewrite compose_nil_nil.
        now rewrite IHf.
      * rewrite compose_nil_ari, compose_nil_nil.
        repeat rewrite compose_nil_ari.
        now rewrite IHf.
    - rewrite compose_ari.
      repeat rewrite compose_nil_ari.
      rewrite compose_ari.
      now rewrite IHf.
  + repeat rewrite compose_ari. 
    now rewrite IHf.
Defined.

Fixpoint compose_restr {n p q} (Hp : p <= q) (Hq : q <= n) 
  (a a' : arity) : 
  compose (restr a' q.+1 n.+1 (⇑ Hq)) (restr a p n (Hp ↕ Hq)) = 
  compose (restr a p n.+1 (Hp ↕ ↑Hq)) (restr a' q n Hq).
Proof.
  revert n q Hp Hq.
  induction p; intros n q Hp Hq.
  + repeat rewrite restr_0.
    rewrite restr_suc.
    rewrite compose_nil_ari, compose_ari.
    rewrite compose_idl, compose_idr.
    reflexivity.
  + invert_le Hp.
    invert_le Hq.
    repeat rewrite restr_suc.
    repeat rewrite compose_nil_nil.
    rewrite <-restr_suc.
    exact (f_equal nil_cons (IHp n q (⇓ Hp) (⇓ Hq))).
Qed.

Fixpoint makeF1_aux (k : nat) 
  (F0 : nat -> HSet)
  (F1 : forall p n, arity -> p <= n -> F0 (n.+1) -> F0 n) :
  forall p n, Hom p n -> F0 (k + n) -> F0 (k + p).
Proof.
  intros p n f X.
  destruct f.
  + exact X.
  + rewrite add_succ_r in X|-*.
    exact (makeF1_aux k.+1 F0 F1 p n f X).
  + apply (F1 k (k + p) a (leR_m k)).
    rewrite add_succ_r in X.
    exact (makeF1_aux k.+1 F0 F1 p n f X).
Defined.

Definition makeF1_aux_ari (k : nat)
  (F0 : nat -> HSet)
  (F1 : forall p n, arity -> p <= n -> F0 (n.+1) -> F0 n)
  (p n : nat) (a : arity) (f : Hom p n) (X : F0 (k + n.+1)) :
  makeF1_aux k F0 F1 p n.+1 (ari_cons a f) X =
  F1 k (k + p) a (leR_m k) (makeF1_aux k.+1 F0 F1 p n f (rew [F0] add_succ_r _ _ in X)) := eq_refl.

Definition makeF1_aux_nil (k : nat)
  (F0 : nat -> HSet)
  (F1 : forall p n, arity -> p <= n -> F0 (n.+1) -> F0 n)
  (p n : nat) (f : Hom p n) (X : F0 (k + n.+1)) :
  makeF1_aux k F0 F1 p.+1 n.+1 (nil_cons f) X =
  rew <-[F0] add_succ_r _ _ in 
    makeF1_aux k.+1 F0 F1 p n f (rew [F0] add_succ_r _ _ in X) := eq_refl.

Lemma leR_rew {p q n : nat} (H : n = q) (Hp : p <= n) : p <= q.
Proof.
  rewrite <-H. exact Hp.
Qed.

Lemma F1_subst 
  (F0 : nat -> HSet)
  (F1 : forall p n, arity -> p <= n -> F0 (n.+1) -> F0 n)
  (p q n : nat) (a : arity) (H : n = q) (Hp : p <= n)
  (X : F0 n.+1) :
  rew [F0] H in F1 p n a Hp X = 
  F1 p q a (leR_rew H Hp) (rew [F0] (f_equal S H) in X).
Proof.
  now destruct H.
Qed.

Definition makeF1_aux_helper (k k' : nat) (Hk : k' <= k) 
  (F0 : nat -> HSet)
  (F1 : forall p n, arity -> p <= n -> F0 (n.+1) -> F0 n)
  (F1_correct : forall p q n (Hp : p <= q) (Hq : q <= n)
    (a a' : arity) (X : F0 (n.+2)), 
    F1 p n a (Hp ↕ Hq) (F1 q.+1 n.+1 a' Hq X) = 
    F1 q n a' Hq (F1 p n.+1 a (Hp ↕ ↑ Hq) X)) :
  forall (p n : nat) (a : arity) (f : Hom p n) (X : F0 (k.+1 + n)),
  makeF1_aux k F0 F1 p n f (F1 k' (k + n) a (leR_raise_k n Hk) X) =
  F1 k' (k + p) a (leR_raise_k p Hk) (makeF1_aux k.+1 F0 F1 p n f X).
Proof.
  intros p n a f X.
  revert k k' Hk X.
  induction f; intros k k' Hk X.
  + reflexivity.
  + repeat rewrite makeF1_aux_nil.
    rewrite (F1_subst F0 F1).
    rewrite (IHf k.+1 k' (↑ Hk)).
    unfold eq_rect_r.
    rewrite (F1_subst F0 F1).
    rewrite (UIP_nat _ _ _ (eq_sym (add_succ_r k.+1 p))).
    now rewrite (UIP_nat _ _ _ (add_succ_r k.+1 n)).
  + repeat rewrite makeF1_aux_ari.
    rewrite (F1_subst F0 F1).
    rewrite (IHf k.+1 k' (↑ Hk)).
    rewrite (F1_correct k' k (k + p) (⇑ Hk) _ a a0).
    now rewrite (UIP_nat _ _ _ (add_succ_r k.+1 n)).
Qed.

Fixpoint makeF1_aux_correct (k : nat)
  (F0 : nat -> HSet)
  (F1 : forall p n, arity -> p <= n -> F0 (n.+1) -> F0 n)
  (F1_correct : forall p q n (Hp : p <= q) (Hq : q <= n)
    (a a' : arity) (X : F0 (n.+2)), 
    F1 p n a (Hp ↕ Hq) (F1 q.+1 n.+1 a' Hq X) = 
    F1 q n a' Hq (F1 p n.+1 a (Hp ↕ ↑ Hq) X)) :
  forall (p q n : nat) (g : Hom q n) (f : Hom p q) (X : F0 (k + n)), 
    makeF1_aux k F0 F1 _ _ f (makeF1_aux k F0 F1 _ _ g X) = 
    makeF1_aux k F0 F1 _ _ (compose g f ) X.
Proof.
  intros p q n g f X.
  destruct g.
  + reflexivity.
  + Hom_destruct f.
    - rewrite compose_nil_nil.
      repeat rewrite makeF1_aux_nil.
      rewrite rew_opp_r.
      now rewrite (makeF1_aux_correct k.+1 F0 
        F1 F1_correct _ _ _ g f _).
    - rewrite compose_nil_ari.
      repeat rewrite makeF1_aux_ari.
      rewrite makeF1_aux_nil.
      rewrite rew_opp_r.
      now rewrite (makeF1_aux_correct k.+1 F0
        F1 F1_correct _ _ _ g f _).
  + rewrite compose_ari.
    repeat rewrite makeF1_aux_ari.
    rewrite <-(makeF1_aux_correct k.+1 F0 
        F1 F1_correct p p0 n g f _).
    now rewrite (makeF1_aux_helper k k (leR_refl) F0 F1 F1_correct _ _ a f).
Qed.

Definition makeF1
  (F0 : nat -> HSet)
  (F1 : forall p n, arity -> p <= n -> F0 n.+1 -> F0 n) :
  forall p n, Hom p n -> F0 n -> F0 p := makeF1_aux 0 F0 F1.

Definition makeF1_correct
  (F0 : nat -> HSet)
  (F1 : forall p n, arity -> p <= n -> F0 (n.+1) -> F0 n)
  (F1_correct : forall p q n (Hp : p <= q) (Hq : q <= n)
    (a a' : arity) (X : F0 (n.+2)), 
    F1 p n a (Hp ↕ Hq) (F1 q.+1 n.+1 a' Hq X) = 
    F1 q n a' Hq (F1 p n.+1 a (Hp ↕ ↑ Hq) X)) :
  forall (p q n : nat) (g : Hom q n) (f : Hom p q) (X : F0 n), 
    makeF1 F0 F1 _ _ f (makeF1 F0 F1 _ _ g X) = 
    makeF1 F0 F1 _ _ (compose g f ) X := makeF1_aux_correct 0 F0 F1 F1_correct.

Record Presheaf := {
  F0 : nat -> HSet;
  F1 {p n : nat} : Hom p n -> F0 n -> F0 p;
  F1_id {n : nat} {X : F0 n} : F1 (id n) X = X; 
  F1_compose {n p q} {X : F0 n} (g : Hom q n) (f : Hom p q) : 
    F1 f (F1 g X) = F1 (compose g f) X; 
}.

End Category.