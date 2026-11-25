/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientChange.CoefficientOperationComparisons
public import WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCompletion
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Reduction

/-!
# Canonical coefficient comparisons for the six-functor transformations

Source: the adopted `AlgebraicGeometry.coefficientChangeCompatibility` docstring and fields.
The latest blueprint `proposition-six-operations-change-coefficients` supplies the route on its
narrower stages.
-/

@[expose] public section
set_option autoImplicit false
universe u

-- Normalize quotient coefficient instances as in IntegralCoefficients.
attribute [local instance 2000] CommRing.toRing
open CategoryTheory Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.CoefficientChange

set_option hygiene false in
local notation "DE(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} A))
set_option hygiene false in
local notation "DP(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))

/-- The component of the actual compact-support projection transformation. -/
noncomputable abbrev projection (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (K : DE(X, A)) (L : DE(Y, A)) :=
  ((Etale.projectionMap (ModuleCat.{u + 1} A) f).app K).app L

end AlgebraicGeometry.CoefficientChange
