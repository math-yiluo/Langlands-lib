/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.FiniteRealization.DiagonalRootRouteInsertions
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # Exact single and shift coherence for root insertion squares

Source: exact-functor single comparisons and coefficient changes (1).
(blueprint: lem-diagonal-shifted-root-insertion-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem shifted_square
    {B D E : Type*} [Category B] [Category D] [Category E]
    [HasShift B ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (Q : E ⥤ B) (R : D ⥤ B) (H : E ⥤ D)
    [Q.CommShift ℤ] [R.CommShift ℤ] [H.CommShift ℤ]
    (σ : Q ⟶ H ⋙ R) [NatTrans.CommShift σ ℤ]
    {X : B} {Y : E} {Z Z' : D}
    (f : X ⟶ Q.obj Y) (g : X ⟶ R.obj Z) (e : H.obj Y ⟶ Z') (h : Z ⟶ Z')
    (hh : f ≫ σ.app Y ≫ R.map e = g ≫ R.map h) (n : ℤ) :
    f⟦n⟧' ≫ (Q.commShiftIso n).inv.app Y ≫ σ.app (Y⟦n⟧) ≫
      R.map ((H.commShiftIso n).hom.app Y ≫ e⟦n⟧') =
    g⟦n⟧' ≫ (R.commShiftIso n).inv.app Z ≫ R.map (h⟦n⟧') := by
  have hc : R.map ((H.commShiftIso n).inv.app Y) ≫
      R.map ((H.commShiftIso n).hom.app Y) = 𝟙 _ := by
    rw [← R.map_comp, Iso.inv_hom_id_app, R.map_id]
  rw [NatTrans.app_shift σ n Y]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    Functor.commShiftIso_comp_inv_app, R.map_comp]
  rw [reassoc_of% hc]
  have he := (R.commShiftIso n).inv.naturality e
  have ht := (R.commShiftIso n).inv.naturality h
  change (R.map e)⟦n⟧' ≫ (R.commShiftIso n).inv.app Z' =
    (R.commShiftIso n).inv.app (H.obj Y) ≫ R.map (e⟦n⟧') at he
  change (R.map h)⟦n⟧' ≫ (R.commShiftIso n).inv.app Z' =
    (R.commShiftIso n).inv.app Z ≫ R.map (h⟦n⟧') at ht
  rw [← he, ← ht]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun z ↦ z⟦n⟧' ≫ (R.commShiftIso n).inv.app Z') hh

/-- An ordinary insertion square gives its exact derived square after shifting.

Source: coefficient changes (1), exact single and shift coherence.
(blueprint: lem-diagonal-shifted-root-insertion-comparison).
Proof: compose with the monic right single comparison, and use the composition and
natural-isomorphism single coherence to turn the ordinary equality into its degree-zero
derived equality. Shift it, use the shift compatibility of the induced natural
isomorphism and composition comparison, and cancel inverse shift comparisons. -/
theorem shiftedRootInsertion_comparison
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (Q : E ⥤ C) (R : D ⥤ C) (H : E ⥤ D)
    [Q.Additive] [R.Additive] [H.Additive]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (s : Q ≅ H ⋙ R) {M : C} {N : E} {L : D}
    (f : M ⟶ Q.obj N) (g : M ⟶ R.obj L) (h : L ⟶ H.obj N)
    (hh : f ≫ s.hom.app N = g ≫ R.map h) :
    shiftedRootInsertion Q f ≫
      (Functor.mapDerivedCategoryNatIso s ≪≫ (Functor.mapDerivedCategoryCompIso H R).symm).hom.app
        (((DerivedCategory.singleFunctor E 0).obj N)⟦(2 : ℤ)⟧) ≫
      R.mapDerivedCategory.map
        ((H.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ ≫
          ((H.mapDerivedCategorySingleFunctor 0).hom.app N)⟦(2 : ℤ)⟧') =
    shiftedRootInsertion R g ≫
      R.mapDerivedCategory.map (((DerivedCategory.singleFunctor D 0).map h)⟦(2 : ℤ)⟧') := by
  let σ := (Functor.mapDerivedCategoryNatIso s ≪≫
    (Functor.mapDerivedCategoryCompIso H R).symm).hom
  have hz :
      ((DerivedCategory.singleFunctor C 0).map f ≫
          (Q.mapDerivedCategorySingleFunctor 0).inv.app N) ≫ σ.app _ ≫
        R.mapDerivedCategory.map ((H.mapDerivedCategorySingleFunctor 0).hom.app N) =
      ((DerivedCategory.singleFunctor C 0).map g ≫
          (R.mapDerivedCategorySingleFunctor 0).inv.app L) ≫
        R.mapDerivedCategory.map ((DerivedCategory.singleFunctor D 0).map h) := by
    apply (cancel_mono ((R.mapDerivedCategorySingleFunctor 0).hom.app (H.obj N))).mp
    simp only [Category.assoc]
    dsimp only [σ, Iso.trans_hom, NatTrans.comp_app]
    simp only [Category.assoc, Iso.symm_hom]
    rw [Functor.mapDerivedCategoryNatIso_comp_hom_app_singleFunctor H R Q s N]
    simp only [Iso.inv_hom_id_app_assoc]
    rw [← (DerivedCategory.singleFunctor C 0).map_comp, hh,
      (DerivedCategory.singleFunctor C 0).map_comp]
    have hn := (R.mapDerivedCategorySingleFunctor 0).hom.naturality h
    change R.mapDerivedCategory.map ((DerivedCategory.singleFunctor D 0).map h) ≫
      (R.mapDerivedCategorySingleFunctor 0).hom.app (H.obj N) =
      (R.mapDerivedCategorySingleFunctor 0).hom.app L ≫
        (DerivedCategory.singleFunctor C 0).map (R.map h) at hn
    rw [hn, Iso.inv_hom_id_app_assoc]
  have : NatTrans.CommShift σ ℤ := by
    dsimp only [σ, Iso.trans_hom]
    infer_instance
  simpa only [shiftedRootInsertion, σ, Category.assoc] using
    shifted_square Q.mapDerivedCategory R.mapDerivedCategory H.mapDerivedCategory σ
    _ _ _ _ hz (2 : ℤ)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
