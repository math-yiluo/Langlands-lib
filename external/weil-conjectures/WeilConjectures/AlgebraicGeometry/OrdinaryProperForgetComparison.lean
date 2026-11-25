/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows

/-! # Proper forget-supports with recorded ordinary endpoints

Source: the canonical proper forget-supports comparison in
WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace

/-- The existing proper forget-supports isomorphism, with the ordinary direct-image
endpoint fixed before taking components. This is precisely the canonical construction:
forget-supports followed by ordinary direct-image composition and congruence.
The original isomorphism supplies both arrows and the inverse identities.
The definition is not irreducible: consumers of `diagonalLift` and
`projectionComparison` identify it with the original isomorphism by `rfl`.
Source: LowerShriekToLowerStar, rightDerivedLowerShriekIsoRightDerivedLowerStar.
(auxiliary; not a blueprint node). -/
noncomputable def ordinaryProperForgetComparison
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ≅ ordinaryFinitePushforward A f :=
  rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) f

end AlgebraicGeometry.Etale
