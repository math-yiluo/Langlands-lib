/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerSystem
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantUnitComp

/-! # The constant-object unit as an ordinary adjunction unit

Source: blueprint proposition-adjunction-projective-line--1, canonical pullback counits.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace
  upperStar lowerStar DerivedCategory.singleFunctors
  ordinaryFiniteUnitPullback singleFunctorCompLeftDerivedUpperStarIso
  leftDerivedUpperStarComp derivedUpperStarLowerStarAdjunction derivedSquareUpperStarIso

/-- The ordinary constant-object unit is the adjunction unit followed by direct
image of the constant-object pullback comparison.
Source: blueprint proposition-adjunction-projective-line--1, substitution of canonical pullback
counits (auxiliary; not a blueprint node).

Proof: apply the existing supportedDerivedUnit_eq for ordinaryFiniteAdjunction.
Unfold only this recorded adjunction wrapper; its value is the specified etale
derived adjunction. The existing theorem already identifies the remaining
composite with the canonical constant-object pullback comparison. -/
theorem supportedDerivedUnit_eq_adjunction (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    supportedDerivedUnit A f =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.app
          (ordinaryFiniteUnit A Y) ≫
        (ordinaryFinitePushforward A f).map (ordinaryFiniteUnitPullback A f).hom := by
  simpa only [ordinaryFiniteAdjunction] using supportedDerivedUnit_eq A f

end AlgebraicGeometry.Etale
