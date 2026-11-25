/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction

/-!
# The full derived adjunction unit evaluated on single objects

Source: Stacks 0A45 (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace CategoryTheory.Adjunction
section
open MonoidalCategory
universe vC vD uC uD
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory.{vC} C] [HasDerivedCategory.{vD} D]
  [HasKInjectiveResolutions D]
  {f : C ⥤ D} {g : D ⥤ C} [f.Additive] [g.Additive]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]

/-- The full derived adjunction unit on X[0], followed by the derived image of c
under the canonical single-object comparison. This names the existing construction
and elaborates its structural instances once; it makes no new choice.
Source: Stacks 0A45 (auxiliary; not a blueprint node). -/
@[irreducible]
def derivedSingleUnit (adj : f ⊣ g) (X : C) (Y : D) (c : f.obj X ⟶ Y) :
    (DerivedCategory.singleFunctor C 0).obj X ⟶
      g.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor D 0).obj Y) :=
  adj.derivedAdjunction.unit.app ((DerivedCategory.singleFunctor C 0).obj X) ≫
    g.rightDerivedFunctor.map (f.singleFunctorCompLeftDerivedFunctorIso.hom.app X ≫
      (DerivedCategory.singleFunctor D 0).map c)

/-- Expand the cached single-object unit to its original full derived composite.
Source: Stacks 0A45 (auxiliary; not a blueprint node).
Proof: unfold the named cache; both sides are the same morphism. -/
theorem derivedSingleUnit_eq (adj : f ⊣ g) (X : C) (Y : D) (c : f.obj X ⟶ Y) :
    derivedSingleUnit adj X Y c =
      adj.derivedAdjunction.unit.app ((DerivedCategory.singleFunctor C 0).obj X) ≫
        g.rightDerivedFunctor.map (f.singleFunctorCompLeftDerivedFunctorIso.hom.app X ≫
          (DerivedCategory.singleFunctor D 0).map c) := by
  unfold derivedSingleUnit
  rfl

end
end CategoryTheory.Adjunction
