/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalComponents
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalCartier
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineTrace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus
public import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
public import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition

/-! # Invertibility of the diagonal source comparison

Source: blueprint lemma-class-diagonal-projective-line, standard-chart Cartier calculation;
lem-sp-tower-p1-arbitrary-base-integrals, steps 2 and 6.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace
  projectiveLineTraceTransport

private theorem isIso_pasted_units
    {C D : Type*} [Category C] [Category D]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ C} {R₂ : C ⥤ D}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : L₁ ⋙ L₂ ≅ 𝟭 C)
    {X : C} {Y : D} {Z : C} (e₁ : L₁.obj X ≅ Y) (e₂ : L₂.obj Y ≅ Z) :
    IsIso ((adj₁.unit.app X ≫ R₁.map e₁.hom) ≫
      R₁.map (adj₂.unit.app Y ≫ R₂.map e₂.hom)) := by
  have : (L₁ ⋙ L₂).Full := Functor.Full.of_iso e.symm
  have : (L₁ ⋙ L₂).Faithful := Functor.Faithful.of_iso e.symm
  have he : (adj₁.unit.app X ≫ R₁.map e₁.hom) ≫
      R₁.map (adj₂.unit.app Y ≫ R₂.map e₂.hom) =
      (adj₁.comp adj₂).unit.app X ≫
        (R₂ ⋙ R₁).map (L₂.map e₁.hom ≫ e₂.hom) := by
    simp only [Adjunction.comp_unit_app, Functor.comp_map, Functor.map_comp, Category.assoc]
    rw [← R₁.map_comp_assoc, ← adj₂.unit_naturality, R₁.map_comp]
    simp only [Category.assoc]
  rw [he]
  infer_instance

section
open MonoidalCategory
universe vC vD uC uD
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [MonoidalCategory D] [MonoidalPreadditive D] [HasCountableCoproducts D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]
  [HasDerivedCategory.{vC} C] [HasDerivedCategory.{vD} D]
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
  {f : C ⥤ D} {g : D ⥤ C} {f' : D ⥤ C} {g' : C ⥤ D}
  [f.Additive] [g.Additive] [f'.Additive] [g'.Additive]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  [PreservesFiniteLimits f'] [PreservesFiniteColimits f']

private theorem isIso_pasted_single_units (adj : f ⊣ g) (adj' : f' ⊣ g')
    (e : f.leftDerivedFunctor ⋙ f'.leftDerivedFunctor ≅ 𝟭 (DerivedCategory C))
    (X : C) (Y : D) (Z : C) (c : f.obj X ≅ Y) (c' : f'.obj Y ≅ Z) :
    IsIso (adj.derivedSingleUnit X Y c.hom ≫
      g.rightDerivedFunctor.map (adj'.derivedSingleUnit Y Z c'.hom)) := by
  rw [Adjunction.derivedSingleUnit_eq, Adjunction.derivedSingleUnit_eq]
  exact isIso_pasted_units adj.derivedAdjunction adj'.derivedAdjunction e
    (f.singleFunctorCompLeftDerivedFunctorIso.app X ≪≫
      (DerivedCategory.singleFunctor D 0).mapIso c)
    (f'.singleFunctorCompLeftDerivedFunctorIso.app Y ≪≫
      (DerivedCategory.singleFunctor C 0).mapIso c')
end

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] projectiveLineDiagonalAlpha ordinaryFiniteUnitPullback
  derivedUpperStarLowerStarAdjunction

/-- The canonical source comparison for the diagonal is an isomorphism over every base.
Source: blueprint lemma-class-diagonal-projective-line, derived-composition identification alpha.
(auxiliary; not a blueprint node)

Proof: each projection composed with the diagonal is identity. The corresponding
composite inverse-image functor is therefore naturally isomorphic to identity,
so its adjunction unit is invertible. Expand the two constant-object units in alpha.
Naturality of the second unit rewrites their composite as the composite adjunction
unit followed by direct image of the two constant-object comparison isomorphisms.
Every factor is invertible. No compatibility choice or Noetherian hypothesis is needed. -/
theorem isIso_projectiveLineDiagonalAlpha (A : Type (u + 1)) [CommRing A]
    (S : Scheme.{u}) (a : Bool) :
    IsIso (C := DerivedCategoryModule A (ProjectiveLine S))
      (projectiveLineDiagonalAlpha A S a) := by
  let p := projectiveLineDiagonalProjection S a
  let i := pullback.diagonal (ProjectiveLine S ↘ S)
  have hi : i ≫ p = 𝟙 (ProjectiveLine S) := by
    cases a <;> simp only [i, p, projectiveLineDiagonalProjection,
      pullback.diagonal_fst, pullback.diagonal_snd]
  let eId : (upperStar (ModuleCat.{u + 1} A) (𝟙 (ProjectiveLine S))).leftDerivedFunctor ≅
      𝟭 (DerivedCategoryModule A (ProjectiveLine S)) :=
    Functor.leftDerivedFunctorNatIso _
        (upperStarId (ModuleCat.{u + 1} A) (ProjectiveLine S)) ≪≫
      (𝟭 _).leftDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _
  let e := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i p
    (𝟙 (ProjectiveLine S)) hi.symm).symm ≪≫ eId
  unfold projectiveLineDiagonalAlpha constantSingleSectionUnits
  exact isIso_pasted_single_units
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i) e
    (ordinaryFiniteConstant A (ProjectiveLine S))
    (ordinaryFiniteConstant A
      (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))
    (ordinaryFiniteConstant A (ProjectiveLine S))
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) p).app (ModuleCat.of A A))
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).app (ModuleCat.of A A))

end AlgebraicGeometry.Etale
