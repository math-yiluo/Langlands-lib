/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.Adjunction.MateCompCoherence

/-!
# The derived adjunction of an exact left adjoint

For an adjunction `adj : f ⊣ g` of additive functors between abelian categories with `f` exact,
there are two derived adjunctions with right adjoint `Rg`: the derived adjunction
`Lf ⊣ Rg` (`CategoryTheory.Adjunction.derivedAdjunction`), with left adjoint the total left
derived functor of `f`, and the adjunction `D(f) ⊣ Rg`
(`CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction`), with left adjoint the
functor induced by `f`. They agree through the identification `Lf ≅ D(f)`
(`CategoryTheory.Adjunction.derivedAdjunction_ofNatIsoLeft`,
`CategoryTheory.Adjunction.derivedAdjunction_eq_ofNatIsoLeft`): both units are characterized
by their compatibility with the unit of `adj` on the images of complexes.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Abelian

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasKInjectiveResolutions D]
  {f : C ⥤ D} {g : D ⥤ C} [f.Additive] [g.Additive]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]

/-- **The derived adjunction of an exact left adjoint.** Transported along the identification
`Lf ≅ D(f)` of the total left derived functor of the exact functor `f` with the functor induced
by `f`, the derived adjunction `Lf ⊣ Rg` is the adjunction `D(f) ⊣ Rg`. -/
lemma derivedAdjunction_ofNatIsoLeft (adj : f ⊣ g) :
    adj.derivedAdjunction.ofNatIsoLeft f.leftDerivedFunctorIsoMapDerivedCategory =
      adj.mapDerivedCategoryRightDerivedAdjunction := by
  ext1
  apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
  intro X
  rw [← cancel_mono (g.rightDerivedFunctor.map (f.mapDerivedCategoryFactorsh.hom.app X))]
  have h₁ := (adj.mapHomotopyCategory (ComplexShape.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) f.leftDerivedFunctorCounit
    g.rightDerivedFunctorUnit X
  have h₂ := (adj.mapHomotopyCategory (ComplexShape.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) f.mapDerivedCategoryFactorsh.hom
    g.rightDerivedFunctorUnit X
  have h₃ := NatTrans.congr_app f.leftDerivedFunctorIsoMapDerivedCategory_hom_fac X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₃
  simp only [ofNatIsoLeft_unit, NatTrans.comp_app, Functor.whiskerRight_app, Category.assoc,
    ← Functor.map_comp, h₃]
  exact h₁.trans h₂.symm

/-- **The derived adjunction of an exact left adjoint**, as the adjunction `D(f) ⊣ Rg`
transported along the identification `D(f) ≅ Lf`. -/
lemma derivedAdjunction_eq_ofNatIsoLeft (adj : f ⊣ g) :
    adj.derivedAdjunction = adj.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoLeft
      f.leftDerivedFunctorIsoMapDerivedCategory.symm := by
  rw [← derivedAdjunction_ofNatIsoLeft, ofNatIsoLeft_ofNatIsoLeft_symm]

end CategoryTheory.Adjunction
