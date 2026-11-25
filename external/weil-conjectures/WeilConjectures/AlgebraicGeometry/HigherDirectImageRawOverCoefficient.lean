/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawOverComplex

/-! # The fixed coefficient morphism for raw pullback over W

Source: Stacks Project, Tags 03Q8 and 09Z1, composition of inverse images.
(blueprint: def-sbc-higher-image-raw-over-coefficient).
-/

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true

/-- The single-complex comparison followed by the fixed identification of restricted
coefficients. Its explicit type keeps the constructed coefficient map folded.
Source: Stacks Project, Tags 03Q8 and 09Z1, inverse-image composition.
(blueprint: def-sbc-higher-image-raw-over-coefficient). -/
noncomputable def higherDirectImageRawOverCoefficient
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {A B : Over W} (f : A ⟶ B) :
    D+((f.left)^*[ModuleCat.{u + 1} Λ]).obj
        (higherDirectImageRawOverComplex Λ G B) ⟶ higherDirectImageRawOverComplex Λ G A :=
  (((f.left)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
    (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp (ModuleCat.{u + 1} Λ) f.left B.hom A.hom
        (Over.w f).symm).inv.app G)

/-- The shared coefficient has the original formula, including its original endpoints.
The heterogeneous equality permits transport of the endpoints by the complex equation.
Source: Stacks Project, Tags 03Q8 and 09Z1, inverse-image composition.
(blueprint: def-sbc-higher-image-raw-over-coefficient).
Proof: Unfold the concrete coefficient; both maps are the same composite. -/
theorem higherDirectImageRawOverCoefficient_heq
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {A B : Over W} (f : A ⟶ B) :
    HEq (higherDirectImageRawOverCoefficient Λ G f) (
  (((f.left)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
    (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp (ModuleCat.{u + 1} Λ) f.left B.hom A.hom
        (Over.w f).symm).inv.app G)) := by rfl

end AlgebraicGeometry.Etale
