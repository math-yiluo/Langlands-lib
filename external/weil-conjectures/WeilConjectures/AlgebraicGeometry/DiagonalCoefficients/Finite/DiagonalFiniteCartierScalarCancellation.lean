/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientArrowTransport
import WeilConjectures.AlgebraicGeometry.ScalarUnitExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.AlgebraicGeometry.ExactFunctorDerivedUnit
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierScalarUnitDerivedUnit

/-! # Cancellation of normalized finite Cartier scalar adjuncts

Source: coefficient changes (1).
(blueprint: lem-diagonal-finite-cartier-scalar-cancellation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] geoCartierConstant geoCartierLine

/-- Two quotient classes with the same normalized scalar adjunct are equal.
Source: coefficient changes (1), and the supported Cartier scalar unit
(blueprint: lem-diagonal-finite-cartier-scalar-cancellation).
Proof: Extract the normalized source and root maps and the supported unit from
the given Cartier scalar compatibility. Apply the other square to these same
maps. Convert the supported Cartier scalar unit to the exact-functor DerivedUnit
property. Its degree-two Ext bijection is injective. The two squares give equal
images under this injection, since they have the same right-hand side. -/
theorem class_eq_of_scalar_square
    {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A) {N : ℕ} {hR : (N : R) = 0} {hA : (N : A) = 0}
    {Y : Scheme.{u}} (cR : GeoCartierClass R N hR (diagonalImmersion Y))
    (cA cA' : GeoCartierClass A N hA (diagonalImmersion Y))
    (hcompat : GeoCartierScalarCompatibility φ N hR hA (diagonalImmersion Y) cR cA')
    (hsq : ∀ maps : CartierScalarMaps φ N hR hA Y, maps.Equation cR cA) :
    cA = cA' := by
  unfold GeoCartierScalarCompatibility at hcompat
  obtain ⟨η, θ, hη, hθ, hηunit, _hθunit, hsquare⟩ := hcompat
  let maps : CartierScalarMaps φ N hR hA Y := ⟨η, θ, hη, hθ⟩
  have h := hsq maps
  unfold CartierScalarMaps.Equation at h
  dsimp only [maps] at h
  let U := Sheaf.restrictScalars (Scheme.ProEt.topology (diagonalSurface Y)) φ
  let G := (lowerStar (ModuleCat.{u + 1} R) (diagonalImmersion Y)).obj
    (geoCartierConstant R (ProjectiveLine Y))
  let H := (lowerStar (ModuleCat.{u + 1} A) (diagonalImmersion Y)).obj
    (geoCartierConstant A (ProjectiveLine Y))
  let η' : G ⟶ U.obj H :=
    (lowerStar (ModuleCat.{u + 1} R) (diagonalImmersion Y)).map η
  have hunit : U.DerivedUnit G H η' :=
    geoCartierScalarUnit_derivedUnit φ (diagonalSurface Y) G H η' hηunit
  exact (scalar_unit_ext_bijective U (F := G) (P := H)
    (Q := geoCartierLine A N hA (diagonalSurface Y))
    η' hunit 2).injective (h.trans hsquare.symm)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
