/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Ambient exceptional right adjoint datum

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-def-sf-operations`, order 1488
(blueprint: def-weil-ambient-exceptional-adjoint).

The canonical compact-support candidate uses the ordinary unbounded derived category of
modules over the constant coefficient sheaf. No compactification-independence theorem or
preservation theorem is used: the right adjoints and their coherent comparison maps are
data, and the predicate asks whether such data exist.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The finite-level compact-support candidate for a specified compactification: the
termwise descent of extension by zero followed by the ordinary K-injective right derived
direct image. Source: blueprint order 1488
(blueprint: def-weil-ambient-exceptional-adjoint). -/
noncomputable def sfAmbientCompactSupportCandidate
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (d : Compactification f) : proEtaleDerivedCategory X A ⥤ proEtaleDerivedCategory Y A :=
  (sfIntrinsicExtensionByZero d.i A).mapDerivedCategory ⋙
    proEtaleConstantDerivedDirectImage d.g A

end AlgebraicGeometry.Scheme
