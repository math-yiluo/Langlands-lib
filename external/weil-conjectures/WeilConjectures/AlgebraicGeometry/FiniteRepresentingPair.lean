/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude

/-! # Representing pairs for ordinary finite coefficients

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-def-sp-representing-pair/_section.md, Definition
Representing objects, entire definition (blueprint: definition-representing-objects).

Both the representing object and K are ambient unbounded objects. Only the test object
is bounded constructible of finite Tor amplitude. No base-field or existence hypothesis
is part of this definition; a compactification specifies the existing Rf! convention.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- An ambient object with a specified counit representing Hom(Rf!(-), K) on all finite
ctf tests, on the small etale site. Source: Definition Representing objects, entire text
(blueprint: definition-representing-objects). -/
structure FiniteRepresentingPair (ell n : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Smooth f] (c : Compactification f)
    (K : DerivedCategoryModule (ULift.{u + 1} (ZMod (ell ^ n))) Y) where
  /-- The representing object is ambient, not assumed constructible. -/
  object : DerivedCategoryModule (ULift.{u + 1} (ZMod (ell ^ n))) X
  /-- The specified compact-support counit. -/
  counit : (rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ n)))) c).obj object ⟶ K
  /-- Exactly b maps to Rf!(b) followed by counit, on all Dctf tests. -/
  map_bijective : ∀ M : DerivedCategoryModule (ULift.{u + 1} (ZMod (ell ^ n))) X,
    DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod (ell ^ n))) X M →
    (∃ a b : ℤ, a ≤ b ∧
      DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} (ZMod (ell ^ n))) X a b M) →
    Function.Bijective (fun b : M ⟶ object ↦
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ n)))) c).map b ≫ counit)

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

/-- An ambient object with a specified counit representing Hom(Rf!(-), K) on every
intrinsically constructible bounded finite-Tor test, on the small pro-etale site.
Source: Definition Representing objects, entire text
(blueprint: definition-representing-objects). -/
structure FiniteRepresentingPair (ell n : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Smooth f] (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ n)))))) where
  /-- The representing object is ambient, not assumed constructible. -/
  object : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
    (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ n)))))
  /-- The specified compact-support counit. -/
  counit : (rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ n)))) c).obj object ⟶ K
  /-- Exactly b maps to Rf!(b) followed by counit, on all Dctf tests. -/
  map_bijective : ∀ M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ n))))),
    DerivedCategory.boundedConstructibleIntrinsic (ULift.{u + 1} (ZMod (ell ^ n))) X M →
    (∃ a b : ℤ, a ≤ b ∧ _root_.DerivedCategory.torAmplitudeIn
      (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ n))))) a b M) →
    Function.Bijective (fun b : M ⟶ object ↦
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ n)))) c).map b ≫ counit)

end AlgebraicGeometry.ProEtale
