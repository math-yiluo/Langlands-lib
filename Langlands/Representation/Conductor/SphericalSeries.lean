import Langlands.Representation.Conductor.SphericalCompact
import Mathlib.RingTheory.LaurentSeries

/-! # The actual spherical Laurent series of a smooth model vector -/

noncomputable section

namespace Langlands.Conductor

open MeasureTheory Langlands.GeneralLinear Langlands.Whittaker
open Langlands.HarmonicAnalysis Langlands.RankinSelberg
open Langlands.QuotientIntegration

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] {n : ℕ}
variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
variable [MeasurableSpace (upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F)]
variable [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
variable {ϖ : Fˣ} {μ : Measure (LeftUnipotentQuotient n F)}
variable (h : IsJacquetNormalization q ψ abv ϖ μ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
variable (hπ : IsSmooth π) (ℓ : glFunctionals ψ (n + 1) π)
variable (w : (coefficientModel π ℓ).toSubmodule)

/-- Integrate an actual model degree integrand, using its proved finite
value span. No finite-dimensionality or support premise is needed. -/
def degreeCorankOneModelCoefficient (d : ℤ) :
    symmetricTorusSubalgebra (Fin (n + 1)) ℂ := by
  letI := model_degreeCorankOnePolynomialSpan_finite h.uniformizer
    π hπ ψ ℓ abv q h.conductor w d
  exact degreeCorankOneCoefficient ψ abv h.uniformizer q w.val
    h.conductor.1 μ d

theorem degreeCorankOneModelCoefficient_isHomogeneous (d : ℤ) :
    IsSymmetricTorusHomogeneous (Fin (n + 1)) ℂ
      (degreeCorankOneModelCoefficient h π hπ ℓ w d) d := by
  let := model_degreeCorankOnePolynomialSpan_finite h.uniformizer
    π hπ ψ ℓ abv q h.conductor w d
  exact degreeCorankOneCoefficient_isHomogeneous ψ abv h.uniformizer q w.val
    h.conductor.1 μ d

/-- Each unit-tuple specialization is the corresponding actual scalar
degree integral. Scalar integrability is proved from smoothness. -/
theorem symmetricTorusEvaluation_degreeCorankOneModelCoefficient
    (x : Fin (n + 1) → ℂˣ) (d : ℤ) :
    symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      (degreeCorankOneModelCoefficient h π hπ ℓ w d) =
    ∫ t, (if sphericalQuotientDegree h.uniformizer t = d then
      corankOneIntegrand ψ abv w.val
        (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) 0 t
      else 0) ∂μ := by
  let := model_degreeCorankOnePolynomialSpan_finite h.uniformizer
    π hπ ψ ℓ abv q h.conductor w d
  exact symmetricTorusEvaluation_degreeCorankOneCoefficient ψ abv h.uniformizer
    q w.val h.conductor.1 μ d
      (degreeCorankOneModelIntegrand_isScalarIntegrable
        π hπ ψ ℓ abv q h w d) x

/-- The actual integrated coefficients vanish below one common degree. -/
theorem degreeCorankOneModelCoefficient_eq_zero_below :
    ∃ d₀ : ℤ, ∀ d < d₀, degreeCorankOneModelCoefficient h π hπ ℓ w d = 0 := by
  obtain ⟨d₀, hd₀⟩ :=
    model_degreeCorankOnePolynomialIntegrand_eq_zero_below h.uniformizer
      π hπ ψ ℓ abv q h.conductor w
  refine ⟨d₀, fun d hd => ?_⟩
  let := model_degreeCorankOnePolynomialSpan_finite h.uniformizer
    π hπ ψ ℓ abv q h.conductor w d
  apply (Submodule.mem_bot ℂ).mp
  exact finiteSpanCoefficientIntegral_mem μ
    (degreeCorankOnePolynomialIntegrand ψ abv h.uniformizer q w.val h.conductor.1 d)
    ⊥ (fun t => by simp only [hd₀ d hd, Pi.zero_apply, Submodule.zero_mem])

theorem degreeCorankOneModelCoefficient_support_bddBelow :
    BddBelow (Function.support (degreeCorankOneModelCoefficient h π hπ ℓ w)) := by
  obtain ⟨d₀, hd₀⟩ := degreeCorankOneModelCoefficient_eq_zero_below h π hπ ℓ w
  refine ⟨d₀, fun d hd => ?_⟩
  by_contra hn
  exact hd (hd₀ d (lt_of_not_ge hn))

/-- Jacquet's formal Laurent series of actual homogeneous quotient integrals,
with lower-bounded support proved from smoothness and spherical support. -/
def corankOneModelLaurentSeries :
    LaurentSeries (symmetricTorusSubalgebra (Fin (n + 1)) ℂ) :=
  HahnSeries.ofSuppBddBelow (degreeCorankOneModelCoefficient h π hπ ℓ w)
    (degreeCorankOneModelCoefficient_support_bddBelow h π hπ ℓ w)

@[simp] theorem corankOneModelLaurentSeries_coeff (d : ℤ) :
    (corankOneModelLaurentSeries h π hπ ℓ w).coeff d =
      degreeCorankOneModelCoefficient h π hπ ℓ w d := rfl

theorem corankOneModelLaurentSeries_coeff_isHomogeneous (d : ℤ) :
    IsSymmetricTorusHomogeneous (Fin (n + 1)) ℂ
      ((corankOneModelLaurentSeries h π hπ ℓ w).coeff d) d :=
  degreeCorankOneModelCoefficient_isHomogeneous h π hπ ℓ w d

/-- Coefficientwise specialization of the actual Laurent series. -/
def specializedCorankOneModelLaurentSeries (x : Fin (n + 1) → ℂˣ) :
    LaurentSeries ℂ :=
  (corankOneModelLaurentSeries h π hπ ℓ w).map
    (symmetricTorusEvaluation (Fin (n + 1)) ℂ x)

@[simp] theorem specializedCorankOneModelLaurentSeries_coeff
    (x : Fin (n + 1) → ℂˣ) (d : ℤ) :
    (specializedCorankOneModelLaurentSeries h π hπ ℓ w x).coeff d =
    ∫ t, (if sphericalQuotientDegree h.uniformizer t = d then
      corankOneIntegrand ψ abv w.val
        (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) 0 t
      else 0) ∂μ :=
  symmetricTorusEvaluation_degreeCorankOneModelCoefficient h π hπ ℓ w x d

end Langlands.Conductor
