/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientScalars
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalDiagonalRightDerived

/-! # Shared types for normalized scalar squares

These transparent aliases share the derived-category instances before specializing
coefficient rings. Source: diagonal coefficient changes and their full-unit normalization.
(blueprint: def-diagonal-scalar-square-types).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The original full universal model of coefficient direct image.
Source: diagonal coefficient changes (blueprint: def-diagonal-scalar-square-types). -/
abbrev ScalarRightDerived
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    {X S : Scheme.{u}} (f : X ⟶ S) :=
  DiagonalRightDerived (CondensedRing.lowerStar Λ f)

/-- The original normalized square to the canonical target-coefficient model.
Source: diagonal coefficient changes (blueprint: def-diagonal-scalar-square-types). -/
abbrev CanonicalScalarSquare
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    (R : ScalarRightDerived Λ f) :=
  RestrictionSquare a f R (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ' f))

/-- Invertibility of the actual scalar mate on every unbounded complex.
Source: diagonal coefficient changes (blueprint: def-diagonal-scalar-square-types). -/
abbrev ScalarMateIsIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X S : Scheme.{u}} {f : X ⟶ S}
    {R : ScalarRightDerived Λ f} (s : CanonicalScalarSquare a f R) : Prop :=
  ∀ K : DerivedCategory (Modules Λ X), IsIso ((s.mate a).app K)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
