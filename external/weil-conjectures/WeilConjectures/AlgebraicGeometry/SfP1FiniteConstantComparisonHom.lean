/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.SfP1NativeConstantHom
/-! # Finite constant inverse-image comparison -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false

universe u uB
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace

attribute [local irreducible] DerivedCategory.singleFunctors upperStar lowerStar
attribute [local implicit_reducible] ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero

/-- The single-degree constant comparison is the native finite constant comparison.
Source: blueprint thm-amb-p1-adjunction.proof.md, constant-object comparison.
(auxiliary; not a blueprint node).

Proof: the single-degree left-derived comparison is the exact-derived comparison
followed by the exact single-degree comparison. Adjoining the single image of
the sheaf-level constant comparison gives the native constant comparison, by
associativity. First prove this for an abstract coefficient category and then
specialize to modules over A. -/
theorem finiteConstantComparison_hom
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f).hom.app
        (ordinaryFiniteConstant A Y) ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).hom.app
          (ModuleCat.of A A)) =
    (leftDerivedUpperStarSingleConstantSheafIso (ModuleCat.{u + 1} A) f
      (ModuleCat.of A A)).hom := by
  exact nativeConstant_hom (ModuleCat.{u + 1} A) f (ModuleCat.of A A)

end AlgebraicGeometry.Etale.SfP1Transport
