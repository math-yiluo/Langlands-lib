/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfP1IntegralTransportData

/-! # The diagonal lift with fixed ordinary endpoints

Source: the definition of diagonalLift in SfP1IntegralTransportData.
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

namespace SfP1Transport

/-- The defining diagonal lift, expressed using the same canonical proper comparison
with its ordinary endpoint fixed. The inverse coefficient comparison stays intact.
Source: SfP1IntegralTransportData.diagonalLift.
(auxiliary; not a blueprint node).
Proof: unfold the diagonal lift. Its defining body uses the canonical endpoint
comparison and the intact inverse coefficient comparison, so the equation is
reflexive. -/
theorem diagonalLift_eq_ordinaryProperForget
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f) :
    diagonalLift A f i hi =
      (ordinaryProperForgetComparison A (TraceDiagonalDatum.diagonal f)).hom.app
          (derivedTensorUnit (ModuleCat.{u + 1} A) X) ≫
        (ordinaryFinitePushforward A (TraceDiagonalDatum.diagonal f)).map
          (constantComparison A i).inv ≫
        (properExchange A (diagonalSquare f i hi)).inv.app
          (ordinaryFiniteUnit A (ProjectiveLine S)) := by
  unfold diagonalLift
  rfl

end SfP1Transport
end AlgebraicGeometry.Etale
