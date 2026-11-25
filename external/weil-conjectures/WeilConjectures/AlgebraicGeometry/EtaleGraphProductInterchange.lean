/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphProductGeometry

/-! # The canonical interchange through the product graph

Source: Stacks Project, Tag 0F7J, product-grid boundary
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar openImmersionLowerShriek rightDerivedLowerStarComp

namespace EtaleGraphInterchangeDiagram

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  (d₁ d₂ : EtaleGraphInterchangeDiagram f g)
  (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The word F₀ in the product over Z. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev productF₀ : DerivedCategoryModule A X ⥤
    DerivedCategoryModule A (d₁.productG d₂).U :=
  R(((d₁.productH d₂).a)_*[ModuleCat.{u + 1} A]) ⋙
    D((d₁.productE d₂)_!open[ModuleCat.{u + 1} A]) ⋙
      R((d₁.productR d₂)_*[ModuleCat.{u + 1} A])

/-- The inverse exchange for B, under Rr₀, including the two proper compositors.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def productLiftInterchange :
    (d₁.productF d₂).functor A ⋙ R(((d₁.productG d₂).a)_*[ModuleCat.{u + 1} A]) ≅
      d₁.productF₀ d₂ A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
          (d₁.productF d₂).p (d₁.productG d₂).a
          (d₁.productBV d₂ ≫ d₁.productR d₂) (d₁.productBV_productR d₂).symm ≪≫
          (rightDerivedLowerStarComp (ModuleCat.{u + 1} A)
            (d₁.productBV d₂) (d₁.productR d₂)).symm) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (etaleGraphNormalizedProperOpenExchange A (d₁.productF d₂).e
          (d₁.productBW d₂) (d₁.productBV d₂) (d₁.productE d₂)
          (d₁.productB_square d₂)).symm _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
        (d₁.productF d₂).a (d₁.productBW d₂) (d₁.productH d₂).a
        (d₁.productA_productBW d₂)) _

/-- Interchange for Q₀ with its open and proper compositors.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def productSquareInterchange :
    d₁.productF₀ d₂ A ⋙
        (D(((d₁.productG d₂).e)_!open[ModuleCat.{u + 1} A]) ⋙
          R(((d₁.productG d₂).p)_*[ModuleCat.{u + 1} A])) ≅
      (d₁.productH d₂).functor A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (etaleGraphNormalizedProperOpenExchange A (d₁.productK d₂)
            (d₁.productR d₂) (d₁.productP d₂) (d₁.productG d₂).e
            (d₁.product_square d₂)) _ ≪≫
        Functor.associator _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A)
          (d₁.productE d₂) (d₁.productK d₂)).symm ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A)
            (d₁.productE_productK d₂)) _ ≪≫
      Functor.isoWhiskerLeft _
        (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
          (d₁.productP d₂) (d₁.productG d₂).p (d₁.productH d₂).p
          (d₁.productP_productQ d₂)))

/-- The fixed common boundary I₀(G₀ K); it uses the exchanges for B and Q₀,
never a choice of an isomorphism with these endpoints.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def productInterchange :
    (d₁.productF d₂).functor A ⋙ (d₁.productG d₂).functor A ≅
      (d₁.productH d₂).functor A :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (d₁.productLiftInterchange d₂ A) _ ≪≫
    d₁.productSquareInterchange d₂ A

end EtaleGraphInterchangeDiagram

end AlgebraicGeometry.Etale
