/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftData
import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftSuccessor
import Mathlib.Tactic.Ring

/-! # Coherence laws for the signed source-Hom mates

## References

* Stacks Project, Tags 08J9 and 08JC, signed total-tensor evaluation
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u v d
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open CategoryTheory.MonoidalClosed CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

section Coherence
variable {C E : Type*} [Category C] [Category E] [HasShift C ℤ] [HasShift E ℤ]
  {F : C ⥤ E}

private theorem isoAdd_cancel_first {a b c : ℤ} (h : a + b = c)
    (e e' : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor E a)
    (f : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor E b)
    (hh : CommShift.isoAdd' h e f = CommShift.isoAdd' h e' f) : e = e' := by
  apply Iso.ext
  ext X
  apply (shiftFunctor E b).map_injective
  have hx := congr_app (congrArg Iso.hom hh) X
  simp only [CommShift.isoAdd'_hom_app] at hx
  exact (cancel_mono ((shiftFunctorAdd' E a b c h).inv.app (F.obj X))).mp
    ((cancel_epi (f.hom.app (X⟦a⟧))).mp
      ((cancel_epi (F.map ((shiftFunctorAdd' C a b c h).hom.app X))).mp hx))

private theorem coherent_of_successor
    (e : ∀ n : ℤ, shiftFunctor C n ⋙ F ≅ F ⋙ shiftFunctor E n)
    (hz : e 0 = CommShift.isoZero F ℤ)
    (hs : ∀ n : ℤ, e (n + 1) = CommShift.isoAdd (e n) (e 1))
    (m n : ℤ) : e (m + n) = CommShift.isoAdd (e m) (e n) := by
  have hs' (a p : ℤ) (h : a + 1 = p) :
      e p = CommShift.isoAdd' h (e a) (e 1) := by
    subst p
    exact hs a
  have up (b : ℤ) (ih : e (m + b) = CommShift.isoAdd (e m) (e b)) :
      e (m + (b + 1)) = CommShift.isoAdd (e m) (e (b + 1)) := by
    calc
      _ = CommShift.isoAdd' (add_assoc m b 1) (e (m + b)) (e 1) := hs' _ _ _
      _ = CommShift.isoAdd' (add_assoc m b 1)
          (CommShift.isoAdd (e m) (e b)) (e 1) := by rw [ih]
      _ = CommShift.isoAdd (e m) (CommShift.isoAdd (e b) (e 1)) :=
        CommShift.isoAdd'_assoc (e m) (e b) (e 1) rfl rfl (add_assoc m b 1)
      _ = _ := by rw [← hs]
  have down (b : ℤ) (ih : e (m + (b + 1)) = CommShift.isoAdd (e m) (e (b + 1))) :
      e (m + b) = CommShift.isoAdd (e m) (e b) := by
    apply isoAdd_cancel_first (add_assoc m b 1) _ _ (e 1)
    calc
      _ = e (m + (b + 1)) := (hs' _ _ _).symm
      _ = CommShift.isoAdd (e m) (e (b + 1)) := ih
      _ = CommShift.isoAdd (e m) (CommShift.isoAdd (e b) (e 1)) := by rw [hs]
      _ = _ := (CommShift.isoAdd'_assoc (e m) (e b) (e 1)
        rfl rfl (add_assoc m b 1)).symm
  induction n using Int.induction_on with
  | zero =>
    have hb (p : ℤ) (h : m + 0 = p) :
        e p = CommShift.isoAdd' h (e m) (e 0) := by
      have hp : p = m := by omega
      revert h
      rw [hp]
      intro h
      rw [hz]
      exact (CommShift.isoAdd'_isoZero (e m)).symm
    exact hb _ rfl
  | succ b ih => exact up b ih
  | pred b ih =>
    apply down (- (b : ℤ) - 1)
    exact Eq.mpr (congrArg
      (fun t : ℤ ↦ e (m + t) = CommShift.isoAdd (e m) (e t))
      (sub_add_cancel (- (b : ℤ)) 1)) ih

end Coherence

section SignedShift
variable {D : Type d} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
  [MonoidalCategory D] [MonoidalClosed D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int]

private theorem sourceShift_conjugate (K : D) (n : ℤ) :
    (siteHomSourceShift K n).hom =
      conjugateEquiv (ihom.adjunction (K⟦n⟧))
        ((shiftEquiv D n).toAdjunction.comp (ihom.adjunction K))
        (((tensorLeft K).commShiftIso n ≪≫ (siteHomTensorParameterShift K n).symm).hom) := by
  unfold siteHomSourceShift Adjunction.rightAdjointUniq
  ext M
  simp [conjugateEquiv_apply_app, Adjunction.ofNatIsoLeft_unit]

private theorem sourceShift_zero (K M : D) :
    (siteHomSourceShift K 0).hom.app M =
      (MonoidalClosed.pre ((shiftFunctorZero D ℤ).inv.app K)).app M ≫
        (shiftFunctorZero D ℤ).inv.app ((ihom K).obj M) := by
  rw [sourceShift_conjugate]
  suffices
      (shiftFunctorZero D ℤ).inv.app ((ihom (K⟦(0 : ℤ)⟧)).obj M) ≫
        ((shiftFunctorZero D ℤ).inv.app ((ihom (K⟦(0 : ℤ)⟧)).obj M))⟦(0 : ℤ)⟧' ≫
        ((ihom.coev K).app (((ihom (K⟦(0 : ℤ)⟧)).obj M)⟦(0 : ℤ)⟧))⟦(0 : ℤ)⟧' ≫
        ((ihom K).map
          (K ◁ (shiftFunctorZero D ℤ).hom.app ((ihom (K⟦(0 : ℤ)⟧)).obj M)))⟦(0 : ℤ)⟧' ≫
        ((ihom K).map
          ((shiftFunctorZero D ℤ).inv.app K ▷ (ihom (K⟦(0 : ℤ)⟧)).obj M))⟦(0 : ℤ)⟧' ≫
        ((ihom K).map ((ihom.ev (K⟦(0 : ℤ)⟧)).app M))⟦(0 : ℤ)⟧' =
      (pre ((shiftFunctorZero D ℤ).inv.app K)).app M ≫
        (shiftFunctorZero D ℤ).inv.app ((ihom K).obj M) by
    simpa [conjugateEquiv_apply_app, Adjunction.comp_unit_app,
      siteHomTensorParameterShift, Functor.commShiftIso_zero,
      Functor.CommShift.isoZero_hom_app, Functor.CommShift.isoZero_inv_app,
      Equivalence.toAdjunction, shiftEquiv', shiftFunctorCompIsoId_zero_zero_inv_app,
      Category.assoc] using this
  simp only [← Functor.map_comp, ihom.coev_naturality_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id_app]
  simp only [MonoidalClosed.pre, conjugateEquiv_apply_app, ihom.ihom_adjunction_unit,
    ihom.ihom_adjunction_counit, curriedTensor_map_app, Functor.map_comp,
    Category.assoc]
  erw [MonoidalCategory.whiskerLeft_id, (ihom K).map_id,
    (shiftFunctor D 0).map_id]
  rw [Category.id_comp]
  simpa only [MonoidalClosed.pre, conjugateEquiv_apply_app,
    ihom.ihom_adjunction_unit, ihom.ihom_adjunction_counit,
    curriedTensor_map_app, Functor.map_comp, Functor.id_map, Functor.id_obj,
    Category.assoc] using
    ((shiftFunctorZero D ℤ).inv.naturality
      ((MonoidalClosed.pre ((shiftFunctorZero D ℤ).inv.app K)).app M)).symm

private def leftShiftMateIso (K : D) (n : ℤ) :
    (shiftEquiv D n).functor ⋙ tensorLeft K ≅ tensorLeft (K⟦n⟧) :=
  (tensorLeft K).commShiftIso n ≪≫ (siteHomTensorParameterShift K n).symm

omit [MonoidalClosed D] in
private theorem leftShiftMateIso_naturality {K L : D} (f : K ⟶ L) (n : ℤ) :
    Functor.whiskerLeft (shiftEquiv D n).functor ((tensoringLeft D).map f) ≫
        (leftShiftMateIso L n).hom =
      (leftShiftMateIso K n).hom ≫ (tensoringLeft D).map (f⟦n⟧') := by
  ext M
  dsimp only [Functor.whiskerLeft_app, NatTrans.comp_app, leftShiftMateIso,
    Iso.trans_hom, Iso.symm_hom]
  change ((curriedTensor D).map f).app (M⟦n⟧) ≫
      (((curriedTensor D).obj L).commShiftIso n).hom.app M ≫
        (siteHomTensorParameterShift L n).inv.app M =
    ((((curriedTensor D).obj K).commShiftIso n).hom.app M ≫
      (siteHomTensorParameterShift K n).inv.app M) ≫
        ((curriedTensor D).map (f⟦n⟧')).app M
  rw [← Category.assoc, ← NatTrans.shift_app_comm ((curriedTensor D).map f) n M,
    Category.assoc]
  simpa only [siteHomTensorParameterShift, NatIso.ofComponents_inv_app,
    Iso.app_inv, Functor.comp_map, Functor.flip_obj_map, curriedTensor_map_app,
    Category.assoc] using
    congrArg (fun z ↦ ((tensorLeft K).commShiftIso n).hom.app M ≫ z)
      ((((curriedTensor D).flip.obj M).commShiftIso n).inv.naturality f)

private theorem siteHomSourceShift_naturality {K L : D} (f : K ⟶ L) (n : ℤ) :
    pre (f⟦n⟧') ≫ (siteHomSourceShift K n).hom =
      (siteHomSourceShift L n).hom ≫ Functor.whiskerRight (pre f) (shiftFunctor D (-n)) := by
  have hs (K : D) : (siteHomSourceShift K n).hom =
      conjugateEquiv (ihom.adjunction (K⟦n⟧))
        ((shiftEquiv D n).toAdjunction.comp (ihom.adjunction K))
        (leftShiftMateIso K n).hom := by
    exact sourceShift_conjugate K n
  rw [hs K, hs L]
  unfold pre
  change _ = _ ≫ Functor.whiskerRight
    (conjugateEquiv (ihom.adjunction L) (ihom.adjunction K)
      ((tensoringLeft D).map f)) (shiftEquiv D n).inverse
  rw [← conjugateEquiv_whiskerLeft (ihom.adjunction L)
    (ihom.adjunction K) (shiftEquiv D n).toAdjunction]
  calc
    _ = conjugateEquiv _ _
        ((leftShiftMateIso K n).hom ≫ (tensoringLeft D).map (f⟦n⟧')) :=
      conjugateEquiv_comp _ _ _ _ _
    _ = conjugateEquiv _ _
        (Functor.whiskerLeft (shiftEquiv D n).functor ((tensoringLeft D).map f) ≫
          (leftShiftMateIso L n).hom) :=
      congrArg _ (leftShiftMateIso_naturality f n).symm
    _ = _ := (conjugateEquiv_comp _ _ _ _ _).symm

omit [Preadditive D] [MonoidalCategory D] [MonoidalClosed D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int] in
private theorem shiftEquality_naturality (a b : ℤ) (h : a = b)
    {A B : D} (f : A ⟶ B) :
    f⟦a⟧' ≫ (eqToIso (congrArg (shiftFunctor D) h)).hom.app B =
      (eqToIso (congrArg (shiftFunctor D) h)).hom.app A ≫ f⟦b⟧' := by
  subst b
  simp

private theorem oppositeSource_naturality {K L : D} (f : K ⟶ L) (n : ℤ) :
    pre (f⟦-n⟧') ≫ (siteHomOppositeSourceShift K n).hom =
      (siteHomOppositeSourceShift L n).hom ≫
        Functor.whiskerRight (pre f) (shiftFunctor D n) := by
  ext M
  have h := congr_app (siteHomSourceShift_naturality f (-n)) M
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app] at h
  simp only [siteHomOppositeSourceShift, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [← Category.assoc, h, Category.assoc,
    shiftEquality_naturality (- -n) n (neg_neg n) ((pre f).app M), Category.assoc]

private theorem signedSource_naturality (M : D) (n : ℤ)
    (X Y : Dᵒᵖ) (f : X ⟶ Y) :
    let H := internalHom.flip.obj M
    H.map (f⟦n⟧') ≫ siteHomSignedSourceComponent M n Y =
      siteHomSignedSourceComponent M n X ≫ (H.map f)⟦n⟧' := by
  have h := congr_app (oppositeSource_naturality f.unop n) M
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app] at h
  dsimp only [siteHomSignedSourceComponent]
  change (pre (f.unop⟦-n⟧')).app M ≫ _ =
    _ ≫ ((pre f.unop).app M)⟦n⟧'
  simpa only [Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    Units.smul_def] using congrArg (fun z ↦ (n * (n + 1) / 2).negOnePow • z) h

variable [MonoidalPreadditive D]

private def signedSourceIso (M : D) (n : ℤ) :
    shiftFunctor Dᵒᵖ n ⋙ MonoidalClosed.internalHom.flip.obj M ≅
      MonoidalClosed.internalHom.flip.obj M ⋙ shiftFunctor D n :=
  NatIso.ofComponents
    (fun X ↦ (n * (n + 1) / 2).negOnePow •
      (siteHomOppositeSourceShift X.unop n).app M)
    (fun {X Y} f ↦ signedSource_naturality M n X Y f)

private theorem quadratic_sign_successor (m : ℤ) :
    ((m + 1) * (m + 1 + 1) / 2).negOnePow * m.negOnePow =
      (-1 : ℤˣ) * (m * (m + 1) / 2).negOnePow := by
  have hq : (m + 1) * (m + 1 + 1) / 2 = m * (m + 1) / 2 + m + 1 := by
    rw [show (m + 1) * (m + 1 + 1) = m * (m + 1) + (m + 1) * 2 by ring,
      Int.add_mul_ediv_right _ _ (by decide)]
    omega
  rw [hq, Int.negOnePow_add, Int.negOnePow_add]
  calc
    _ = (-1 : ℤˣ) * (m * (m + 1) / 2).negOnePow *
        (m.negOnePow * m.negOnePow) := by simp only [Int.negOnePow_one]; ac_rfl
    _ = _ := by rw [Int.units_mul_self, mul_one]

omit [MonoidalPreadditive D] in
private theorem signedSource_zero (M : D) (X : Dᵒᵖ) :
    siteHomSignedSourceComponent M 0 X =
      (CommShift.isoZero (internalHom.flip.obj M) ℤ).hom.app X := by
  simpa [siteHomSignedSourceComponent, siteHomOppositeSourceShift,
    CommShift.isoZero_hom_app, shiftFunctorZero_op_hom_app, shiftFunctorOpIso,
    internalHom, Functor.flip] using sourceShift_zero X.unop M

private theorem signedSource_successor (M : D) (m : ℤ) (X : Dᵒᵖ) :
    siteHomSignedSourceComponent M (m + 1) X =
      (internalHom.flip.obj M).map ((shiftFunctorAdd Dᵒᵖ m 1).hom.app X) ≫
        siteHomSignedSourceComponent M 1 (X⟦m⟧) ≫
        (siteHomSignedSourceComponent M m X)⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd D m 1).inv.app ((ihom X.unop).obj M) := by
  dsimp only [siteHomSignedSourceComponent]
  rw [siteHom_opposite_source_shift_successor M m X]
  simp only [Functor.map_units_smul, Linear.units_smul_comp,
    Linear.comp_units_smul, smul_smul]
  rw [quadratic_sign_successor]
  simp [mul_comm]

end SignedShift

section SignedShift
variable {D : Type d} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
  [MonoidalCategory D] [MonoidalClosed D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int]

/-- The signed mates have the correct zero component and satisfy addition
coherence, stated before assembling a `CommShift` structure. -/
theorem siteHom_signed_source_shift_laws [MonoidalPreadditive D] (M : D) :
    let H := MonoidalClosed.internalHom.flip.obj M
    (∀ X : Dᵒᵖ, siteHomSignedSourceComponent M 0 X =
      (Functor.CommShift.isoZero H ℤ).hom.app X) ∧
    (∀ (m n : ℤ) (X : Dᵒᵖ), siteHomSignedSourceComponent M (m + n) X =
      H.map ((shiftFunctorAdd Dᵒᵖ m n).hom.app X) ≫
        siteHomSignedSourceComponent M n (X⟦m⟧) ≫
        (siteHomSignedSourceComponent M m X)⟦n⟧' ≫
        (shiftFunctorAdd D m n).inv.app (H.obj X)) := by
  let e := signedSourceIso M
  have hz : e 0 = CommShift.isoZero (internalHom.flip.obj M) ℤ := by
    apply Iso.ext
    ext X
    exact signedSource_zero M X
  have hs (n : ℤ) : e (n + 1) = CommShift.isoAdd (e n) (e 1) := by
    apply Iso.ext
    ext X
    simpa [CommShift.isoAdd_hom_app, e, signedSourceIso,
      siteHomSignedSourceComponent, internalHom, Functor.flip] using
      signedSource_successor M n X
  refine ⟨signedSource_zero M, ?_⟩
  intro m n X
  have h := congr_app (congrArg Iso.hom (coherent_of_successor e hz hs m n)) X
  simpa only [CommShift.isoAdd_hom_app, e, signedSourceIso,
    NatIso.ofComponents_hom_app, Preadditive.smul_iso_hom, Iso.app_hom,
    siteHomSignedSourceComponent] using h

end SignedShift

end AlgebraicGeometry.ProEtale
