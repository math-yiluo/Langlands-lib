/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedExactLift
public import WeilConjectures.CategoryTheory.WeilLiftAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Derived exchanges of an exact adjunction are mates

Let `adj : L ⊣ R` be an adjunction of exact functors between abelian categories, with exchanges
`eL : L ⋙ H ≅ G ⋙ L` and `eR : R ⋙ G ≅ H ⋙ R` against autoequivalences `G`, `H`, such that `eR`
is the right adjoint exchange (mate) of `eL`. Then the derived exchange of `eR`
(`CategoryTheory.Endofunctor.IsoAlgebra.derivedExactCommIso`) is the right adjoint exchange of
the derived exchange of `eL` for the levelwise derived adjunction
`CategoryTheory.Adjunction.mapDerivedCategoryAdjunction`
(`CategoryTheory.Endofunctor.IsoAlgebra.derivedExactCommIso_hom_eq_rightAdjointExchange`).
This is `CategoryTheory.Adjunction.mapDerivedCategoryAdjunction_mate` combined with the
uniqueness of mates (`CategoryTheory.Adjunction.rightAdjointExchange_eq_of_unit`).
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.Endofunctor.IsoAlgebra

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  {G : C ⥤ C} [G.Additive] [G.IsEquivalence] {H : D ⥤ D} [H.Additive] [H.IsEquivalence]
  (eL : L ⋙ H ≅ G ⋙ L) (eR : R ⋙ G ≅ H ⋙ R)

omit [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasKInjectiveResolutions D] in
/-- The derived exchange is the square isomorphism of `MapDerivedCategoryMate`. -/
lemma derivedExactCommIso_eq_mapDerivedCategorySquareIso :
    derivedExactCommIso eR = Functor.mapDerivedCategorySquareIso eR := by
  unfold derivedExactCommIso
  rw [Iso.trans_assoc]

omit [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasKInjectiveResolutions D] in
/-- The square isomorphism of the inverse exchange is the inverse of the derived exchange. -/
lemma mapDerivedCategorySquareIso_symm_hom_app (c : DerivedCategory C) :
    (Functor.mapDerivedCategorySquareIso eL.symm).hom.app c =
      (derivedExactCommIso eL).inv.app c := by
  simp only [Functor.mapDerivedCategorySquareIso, derivedExactCommIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, NatTrans.comp_app]

/-- **Derived exchanges are mates**: if `eR` is the right adjoint exchange of `eL`, the derived
exchange of `eR` is the right adjoint exchange of the derived exchange of `eL` for the levelwise
derived adjunction `D(L) ⊣ D(R)`. -/
theorem derivedExactCommIso_hom_eq_rightAdjointExchange
    (h : Adjunction.rightAdjointExchange adj adj eL = eR.hom) :
    (derivedExactCommIso eR).hom =
      Adjunction.rightAdjointExchange adj.mapDerivedCategoryAdjunction
        adj.mapDerivedCategoryAdjunction (derivedExactCommIso eL) := by
  apply Adjunction.rightAdjointExchange_eq_of_unit
  intro c
  have hβ : ∀ K, adj.unit.app (G.obj K) ≫ R.map (eL.symm.hom.app K) =
      G.map (adj.unit.app K) ≫ eR.hom.app (L.obj K) := fun K ↦ by
    rw [← h]
    exact (Adjunction.map_unit_app_comp_rightAdjointExchange_app adj adj eL K).symm
  have hm := Adjunction.mapDerivedCategoryAdjunction_mate adj adj eR eL.symm hβ c
  have h1 : (Functor.mapDerivedCategorySquareIso eR).hom.app (L.mapDerivedCategory.obj c) =
      (derivedExactCommIso eR).hom.app (L.mapDerivedCategory.obj c) := by
    rw [derivedExactCommIso_eq_mapDerivedCategorySquareIso]
  rw [h1, mapDerivedCategorySquareIso_symm_hom_app] at hm
  exact hm.symm

end CategoryTheory.Endofunctor.IsoAlgebra
