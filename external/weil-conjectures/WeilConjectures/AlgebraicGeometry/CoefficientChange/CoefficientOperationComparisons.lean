/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility

/-!
# Canonical coefficient comparisons for direct images and internal Hom

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

/-- The fixed left adjoint of derived coefficient restriction on the small étale site. -/
noncomputable abbrev etaleExtension {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) : DE(X, A) ⥤ DE(X, B) :=
  ProEtale.pbcFixedScalarExtension X.smallEtaleTopology φ

/-- The principal quotient coefficient map. -/
abbrev quotient (A : Type (u + 1)) [CommRing A] (a : A) (n : ℕ) :=
  Ideal.Quotient.mk (Ideal.span {a} ^ n)

/-- Compact support for a specified compactification, with generic coefficient instances. -/
noncomputable abbrev proCompact (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : DP(X, A) ⥤ DP(Y, A) :=
  ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c

end AlgebraicGeometry.CoefficientChange
