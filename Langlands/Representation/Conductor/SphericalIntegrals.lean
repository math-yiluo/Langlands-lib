import Langlands.Representation.Conductor.SphericalTests
import Langlands.Representation.RankinSelberg.QuotientIntegrals

/-!
# Corank-one integrals of spherical tests

A normalized spherical test in an inverse-character coefficient model is paired
with a vector of a larger standard coefficient model through the actual
corank-one JPSS integral. The quotient measure and the absolute value stay
explicit. No convergence, rational continuation or local factor is asserted.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory

universe uF uV uW

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
variable {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
variable {ℓ' : glInverseFunctionals ψ n σ}

/-- The inverse-character Whittaker function of a normalized spherical test. -/
def sphericalTestWhittaker (w' : SphericalTest σ ℓ') : InverseWhittakerFunctions ψ n :=
  w'.val.val.val

@[simp] theorem sphericalTestWhittaker_apply (w' : SphericalTest σ ℓ')
    (g : Langlands.GeneralLinear (n + 1) F) :
    (sphericalTestWhittaker ψ w').val g = sphericalTestFunction σ ℓ' w' g := rfl

omit [TopologicalSpace F] in
/-- The determinant of an integral invertible matrix has valuation one. -/
theorem valuation_det_of_mem_integralSubgroup {k : Langlands.GeneralLinear (n + 1) F}
    (hk : k ∈ integralSubgroup (ValuativeRel.valuation F).integer n) :
    ValuativeRel.valuation F (Matrix.det k.val) = 1 := by
  obtain ⟨kO, rfl⟩ := hk
  have h := congrArg Units.val
    (Matrix.GeneralLinearGroup.map_det (ValuativeRel.valuation F).integer.subtype kO)
  rw [Matrix.GeneralLinearGroup.val_det_apply] at h
  rw [h]
  exact (Valuation.integer.integers _).valuation_unit (Matrix.GeneralLinearGroup.det kO)

omit [TopologicalSpace F] in
/-- The weight `|det g|^s` is right invariant under the integral group, for an
absolute value equal to one on the valuation units. -/
theorem determinantWeight_mul_integral {abv : AbsoluteValue F ℝ}
    (habv : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1)
    (g k : Langlands.GeneralLinear (n + 1) F)
    (hk : k ∈ integralSubgroup (ValuativeRel.valuation F).integer n) (s : ℂ) :
    determinantWeight abv (g * k) s = determinantWeight abv g s := by
  unfold determinantWeight
  rw [Units.val_mul, Matrix.det_mul, map_mul,
    habv _ (valuation_det_of_mem_integralSubgroup hk), mul_one]

section Restriction

variable (abv : AbsoluteValue F ℝ)
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) W)
variable (ell : glFunctionals ψ (n + 1) π)

/-- Under Jacquet's restriction-invariance clause, the corank-one function of a
spherical test is right invariant under the integral group of the smaller rank. -/
theorem corankOneFunction_sphericalTest_mul_integral
    (habv : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1)
    (w : (coefficientModel π ell).toSubmodule)
    (hw : IsIntegralInvariantOnRestriction π ell w)
    (w' : SphericalTest σ ℓ') (s : ℂ) (g : Langlands.GeneralLinear (n + 1) F)
    (k : integralSubgroup (ValuativeRel.valuation F).integer n) :
    corankOneFunction ψ abv w.val (sphericalTestWhittaker ψ w') s (g * k.val) =
      corankOneFunction ψ abv w.val (sphericalTestWhittaker ψ w') s g := by
  unfold corankOneFunction
  rw [determinantWeight_mul_integral habv g k.val k.property]
  change w.val.val (rankInclusion 1 (g * k.val)) *
      sphericalTestFunction σ ℓ' w' (g * k.val) * _ =
    w.val.val (rankInclusion 1 g) * sphericalTestFunction σ ℓ' w' g * _
  rw [hw g k, sphericalTestFunction_right_invariant σ ℓ' w' k g]

end Restriction

section Integrals

variable (abv : AbsoluteValue F ℝ)
variable [MeasurableSpace (LeftUnipotentQuotient n F)]
variable (μ : Measure (LeftUnipotentQuotient n F))
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) W)
variable (ell : glFunctionals ψ (n + 1) π)

/-- The actual corank-one integral of a larger model vector against a
normalized spherical test of the inverse-character model. -/
def sphericalTestIntegral (w : (coefficientModel π ell).toSubmodule)
    (w' : SphericalTest σ ℓ') (s : ℂ) : ℂ :=
  corankOneModelIntegral ψ abv μ π σ ell ℓ' w w'.val.val s

theorem sphericalTestIntegral_eq (w : (coefficientModel π ell).toSubmodule)
    (w' : SphericalTest σ ℓ') (s : ℂ) :
    sphericalTestIntegral ψ abv μ π ell w w' s =
      ∫ q, corankOneIntegrand ψ abv w.val (sphericalTestWhittaker ψ w') s q ∂μ := rfl

/-- Absolute convergence of the same test integral, not merely existence of
Lean's total Bochner integral. -/
def SphericalTestConverges (w : (coefficientModel π ell).toSubmodule)
    (w' : SphericalTest σ ℓ') (s : ℂ) : Prop :=
  CorankOneConverges ψ abv μ w.val (sphericalTestWhittaker ψ w') s

/-- Convergence on a right half-plane whose threshold may depend on the
actual pair of vectors. -/
def SphericalTestConvergesOnRight (w : (coefficientModel π ell).toSubmodule)
    (w' : SphericalTest σ ℓ') : Prop :=
  ∃ c : ℝ, ∀ s : ℂ, c < s.re → SphericalTestConverges ψ abv μ π ell w w' s

end Integrals

end Langlands.Conductor
