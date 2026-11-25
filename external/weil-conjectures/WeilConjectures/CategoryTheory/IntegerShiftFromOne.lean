/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.Int.Basic

/-! # Extending a degree-one shift comparison

Source: iteration and inverse iteration in the proof of
lem-sc-derived-pullback-tensor-unit-shift, using the shift addition isomorphisms.
(blueprint: lem-sc-integer-shift-from-one).
-/

@[expose] public section
set_option autoImplicit false

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
  (F : C ⥤ D)
local notation "I" n => shiftFunctor C n ⋙ F ≅ F ⋙ shiftFunctor D n
private noncomputable def predecessor (a : I(1 : ℤ)) (n : ℤ) (e : I(n + 1)) : I n :=
  ((whiskeringRight C D D).obj (shiftFunctor D (1 : ℤ))).preimageIso
    (Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Iso.symm a) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (shiftFunctorAdd C n 1).symm F ≪≫ e ≪≫
      isoWhiskerLeft F (shiftFunctorAdd D n 1) ≪≫
      (Functor.associator _ _ _).symm)

private lemma add_predecessor (a : I(1 : ℤ)) (n : ℤ) (e : I(n + 1)) :
    CommShift.isoAdd (predecessor F a n e) a = e := by
  ext X
  simp only [CommShift.isoAdd_hom_app]
  have h := ((whiskeringRight C D D).obj (shiftFunctor D (1 : ℤ))).map_preimage
    (show (shiftFunctor C n ⋙ F) ⋙ shiftFunctor D (1 : ℤ) ⟶
      (F ⋙ shiftFunctor D n) ⋙ shiftFunctor D (1 : ℤ) from
      (Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Iso.symm a) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (shiftFunctorAdd C n 1).symm F ≪≫ e ≪≫
        isoWhiskerLeft F (shiftFunctorAdd D n 1) ≪≫
        (Functor.associator _ _ _).symm).hom)
  have hh := NatTrans.congr_app h X
  dsimp [predecessor, Functor.preimageIso] at hh ⊢
  rw [hh]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← F.map_comp_assoc,
    Iso.hom_inv_id_app, F.map_id, Category.id_comp, Category.comp_id]

private lemma isoAdd'_left_injective {i j k : ℤ} (h : i + j = k)
    (b : I j) {e e' : I i} (he : CommShift.isoAdd' h e b = CommShift.isoAdd' h e' b) :
    e = e' := by
  ext X
  apply (shiftFunctor D j).map_injective
  apply (cancel_mono ((shiftFunctorAdd' D i j k h).inv.app (F.obj X))).1
  apply (cancel_epi (b.hom.app ((shiftFunctor C i).obj X))).1
  apply (cancel_epi (F.map ((shiftFunctorAdd' C i j k h).hom.app X))).1
  simpa only [CommShift.isoAdd'_hom_app, Category.assoc] using
    congrArg (fun t ↦ t.hom.app X) he

private noncomputable def iterated (a : I(1 : ℤ)) (n : ℤ) : I n :=
  Int.inductionOn' n 0 (CommShift.isoZero F ℤ)
    (fun k _ e ↦ CommShift.isoAdd e a)
    (fun k _ e ↦ predecessor F a (k - 1)
      (CommShift.isoAdd' (show k + 0 = k - 1 + 1 by omega) e (CommShift.isoZero F ℤ)))

private lemma iterated_zero (a : I(1 : ℤ)) : iterated F a 0 = CommShift.isoZero F ℤ := by
  exact Int.inductionOn'_self

private lemma iterated_succ (a : I(1 : ℤ)) (n : ℤ) :
    iterated F a (n + 1) = CommShift.isoAdd (iterated F a n) a := by
  by_cases hn : 0 ≤ n
  · exact Int.inductionOn'_add_one hn
  · have hn' : n + 1 ≤ 0 := by omega
    have h := Int.inductionOn'_sub_one (motive := fun n ↦ I n) (z := n + 1)
      (zero := CommShift.isoZero F ℤ)
      (succ := fun k _ e ↦ CommShift.isoAdd e a)
      (pred := fun k _ e ↦ predecessor F a (k - 1)
        (CommShift.isoAdd' (show k + 0 = k - 1 + 1 by omega) e
          (CommShift.isoZero F ℤ))) hn'
    rw! [show n + 1 - 1 = n by omega] at h
    simp only [CommShift.isoAdd'_isoZero] at h
    have hh : iterated F a n = predecessor F a n (iterated F a (n + 1)) := by
      exact h
    rw [hh, add_predecessor]

private lemma iterated_succ' (a : I(1 : ℤ)) (n k : ℤ) (h : n + 1 = k) :
    iterated F a k = CommShift.isoAdd' h (iterated F a n) a := by
  subst k
  exact iterated_succ F a n

private lemma iterated_add' (a : I(1 : ℤ)) (n m k : ℤ) (h : n + m = k) :
    iterated F a k = CommShift.isoAdd' h (iterated F a n) (iterated F a m) := by
  induction m using Int.inductionOn' (b := 0) generalizing k with
  | zero =>
    have hk : k = n := by omega
    cases hk
    rw [iterated_zero]
    exact (CommShift.isoAdd'_isoZero (F := F) (iterated F a n)).symm
  | succ m hm ih =>
    rw [iterated_succ' F a (n + m) k (by omega), ih (n + m) rfl, iterated_succ]
    exact CommShift.isoAdd'_assoc (iterated F a n) (iterated F a m) a
      rfl rfl (by omega)
  | pred m hm ih =>
    apply isoAdd'_left_injective F (show k + 1 = n + m by omega) a
    rw [← iterated_succ' F a k (n + m) (by omega), ih (n + m) rfl]
    rw [CommShift.isoAdd'_assoc (iterated F a n) (iterated F a (m - 1)) a
      h (show m - 1 + 1 = m by omega) (show n + (m - 1) + 1 = n + m by omega)]
    rw [← iterated_succ' F a (m - 1) m (by omega)]


/-- A natural isomorphism commuting with translation by one extends to an integer
shift structure.

Source: the iteration step of lem-sc-derived-pullback-tensor-unit-shift.
(blueprint: lem-sc-integer-shift-from-one).

Proof. Postcomposition with shift by one is fully faithful. Given a comparison
at n+1, compose its hom with the inverse of a and with the source and target
shift addition maps, then take its unique preimage under that postcomposition.
This gives the comparison at n. Functor.map_preimage and cancellation show that
adding a to it recovers the given comparison at n+1. Addition on the right by
any comparison is injective, by faithfulness of its shift and cancellation of
its isomorphisms. Start at the canonical zero comparison and use integer
recursion, adding a upwards and taking the preimage downwards. The successor
identity holds on both sides of zero by the inverse-step calculation. Prove the
addition identity by integer induction on the second summand: the zero case is
the zero identity; the successor case is CommShift.isoAdd'_assoc; the predecessor
case follows by adding a on the right, using associativity and the successor
identity, then cancelling. The comparison at one is a by the left zero identity.
This proves both CommShift equations and works also for zero functors and zero
categories. -/
theorem exists_commShift_of_one
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) (a : shiftFunctor C (1 : ℤ) ⋙ F ≅ F ⋙ shiftFunctor D (1 : ℤ)) :
    ∃ s : F.CommShift ℤ, letI := s
      F.commShiftIso (1 : ℤ) = a := by
  let s : F.CommShift ℤ :=
    { commShiftIso := iterated F a
      commShiftIso_zero := iterated_zero F a
      commShiftIso_add := fun n m ↦ iterated_add' F a n m (n + m) rfl }
  refine ⟨s, ?_⟩
  change iterated F a (0 + 1) = a
  rw [iterated_succ, iterated_zero]
  exact CommShift.isoZero_isoAdd'_ a

end CategoryTheory.Functor
