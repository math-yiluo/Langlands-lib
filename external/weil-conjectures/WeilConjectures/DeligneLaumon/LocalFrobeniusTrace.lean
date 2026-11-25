/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
public import WeilConjectures.ZetaWeil.FrobeniusPointTransport
public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.CoefficientCohomologyModules
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.Topology.JacobsonSpace
public import WeilConjectures.ZetaSeries
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.BigOperators.Finprod

import WeilConjectures.PointCount

/-!
# Local Frobenius on the derived point fibre and its alternating trace

Source: Weil blueprint, sec-poincare-duality/sk-lem-finite,
Local Frobenius and local alternating trace; Deligne, Weil II, (1.1.7)--(1.1.10)
(blueprint: definition-trace-function).

The rational composition comparison below is the localization of the specified integral
comparison. Object equalities only identify the unchanged objects of raw rationalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Identify the prescribed rational pullback object with its integral model.
Source: blueprint rational pullback convention (blueprint: definition-trace-function). -/
def localPullbackObjectIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfRationalConstructibleCategory l E Y) :
    (rationalDerivedPullback l E f).obj K ≅
      (sfRationalConstructibleLocalization l E X).obj
        ((constructibleIntegralPullback l E f).obj K.obj) :=
  eqToIso ((rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 K)

/-- The specified composition comparison, localized from the integral comparison.
Source: blueprint composition convention (blueprint: definition-trace-function). -/
def localPullbackComposition {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (K : sfRationalConstructibleCategory l E Z) :
    (rationalDerivedPullback l E (h ≫ k)).obj K ≅
      (rationalDerivedPullback l E h).obj ((rationalDerivedPullback l E k).obj K) :=
  localPullbackObjectIso l E (h ≫ k) K ≪≫
    (sfRationalConstructibleLocalization l E X).mapIso
      (((integralPullbackComposition l E).choose h k).app K.obj) ≪≫
    (localPullbackObjectIso l E h
      ((sfRationalConstructibleLocalization l E Y).obj
        ((constructibleIntegralPullback l E k).obj K.obj))).symm ≪≫
    (rationalDerivedPullback l E h).mapIso (localPullbackObjectIso l E k K).symm

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

set_option backward.isDefEq.respectTransparency false in
/-- Derived pullback of the underlying Weil complex at an arbitrary geometric point.
Source: blueprint K_xbar (blueprint: definition-trace-function). -/
def localDerivedStalk (K : sfWeilComplex D l hl Y₀ E)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :
    sfRationalConstructibleCategory l E (Spec (.of D.k)) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  (rationalDerivedPullback l E x).obj K.carrier

/-- The bounded finite-dimensional rational point complex C_xbar.
Source: blueprint point-fibre clause (blueprint: definition-trace-function). -/
def localPointComplex (K : sfWeilComplex D l hl Y₀ E)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :
    (DerivedCategory.pointFiniteDimensional E).FullSubcategory :=
  (pointRationalFibre D l hl E).obj (localDerivedStalk l E D hl Y₀ K x)

end WeilConjectures

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

end WeilConjectures
