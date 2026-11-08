import Langlands.Representation.Conductor.SphericalDenominator

/-! # The actual denominator product and its finite coefficient sum -/

noncomputable section

namespace Langlands.Conductor

open scoped BigOperators

universe uK uσ uA uF uV

section FiniteCoefficients

variable {A : Type uA} [CommRing A]

/-- Sum the coefficients of a Laurent series whose actual support is finite. -/
def finiteLaurentCoefficientSum (S : LaurentSeries A)
    (hS : S.support.Finite) : A :=
  ∑ d ∈ hS.toFinset, S.coeff d

/-- A finite Laurent series is exactly the finite sum of its monomials. -/
theorem finiteLaurentSeries_eq_sum (S : LaurentSeries A)
    (hS : S.support.Finite) :
    S = ∑ d ∈ hS.toFinset, HahnSeries.single d (S.coeff d) := by
  classical
  apply HahnSeries.ext
  funext d
  rw [HahnSeries.coeff_sum]
  symm
  trans (HahnSeries.single d (S.coeff d)).coeff d
  · apply Finset.sum_eq_single d
    · intro e _ hed
      exact HahnSeries.coeff_single_of_ne hed.symm
    · intro hd
      have hz : S.coeff d = 0 := by
        simpa only [Set.Finite.mem_toFinset, HahnSeries.mem_support, not_not] using hd
      simpa only [HahnSeries.coeff_single_same] using hz
  · exact HahnSeries.coeff_single_same d (S.coeff d)

end FiniteCoefficients

section Algebra

variable (σ : Type uσ) (K : Type uK) [Fintype σ] [Field K] [Infinite K]

theorem coordinateDenominatorPolynomial_coeff_zero (P : Polynomial K)
    (hP : P.coeff 0 = 1) :
    (coordinateDenominatorPolynomial σ K P).coeff 0 = 1 := by
  apply symmetricTorus_eq_of_evaluations
  intro x
  have he := coordinateDenominatorPolynomial_eval₂ σ K P x 0
  change (coordinateDenominatorPolynomial σ K P).eval₂
    (symmetricTorusEvaluation σ K x).toRingHom 0 = _ at he
  change (symmetricTorusEvaluation σ K x).toRingHom
    ((coordinateDenominatorPolynomial σ K P).coeff 0) = _
  simpa only [Polynomial.eval₂_at_zero, zero_mul,
    ← Polynomial.coeff_zero_eq_eval_zero, hP, Finset.prod_const_one, map_one] using he

/-- Specialization detects coefficientwise equality of these Laurent series. -/
theorem symmetricTorusLaurentSeries_eq_of_specializations
    (S T : LaurentSeries (symmetricTorusSubalgebra σ K))
    (h : ∀ x : σ → Kˣ,
      S.map (symmetricTorusEvaluation σ K x) =
        T.map (symmetricTorusEvaluation σ K x)) : S = T := by
  apply HahnSeries.ext
  funext d
  apply symmetricTorus_eq_of_evaluations
  intro x
  change (S.map (symmetricTorusEvaluation σ K x)).coeff d =
    (T.map (symmetricTorusEvaluation σ K x)).coeff d
  exact congrArg (fun U : LaurentSeries K => U.coeff d) (h x)

/-- A uniform upper bound after every unit-tuple specialization is already
an upper bound over the symmetric Laurent coefficient algebra. -/
theorem symmetricTorusLaurentSeries_coeff_eq_zero_above
    (S : LaurentSeries (symmetricTorusSubalgebra σ K)) (B : ℤ)
    (h : ∀ (x : σ → Kˣ) (d : ℤ), B < d →
      (S.map (symmetricTorusEvaluation σ K x)).coeff d = 0) :
    ∀ d : ℤ, B < d → S.coeff d = 0 := by
  intro d hd
  apply symmetricTorus_eq_of_evaluations
  intro x
  change (S.map (symmetricTorusEvaluation σ K x)).coeff d =
    symmetricTorusEvaluation σ K x 0
  simpa only [map_zero] using h x d hd

theorem symmetricTorusLaurentSeries_support_finite_of_specialized_upper_bound
    (S : LaurentSeries (symmetricTorusSubalgebra σ K))
    (d₀ B : ℤ) (hlo : ∀ d < d₀, S.coeff d = 0)
    (hhi : ∀ (x : σ → Kˣ) (d : ℤ), B < d →
      (S.map (symmetricTorusEvaluation σ K x)).coeff d = 0) :
    S.support.Finite := by
  apply (Set.finite_Icc d₀ B).subset
  intro d hd
  have hn : S.coeff d ≠ 0 := hd
  constructor
  · by_contra h
    exact hn (hlo d (lt_of_not_ge h))
  · by_contra h
    exact hn (symmetricTorusLaurentSeries_coeff_eq_zero_above σ K S B hhi d
      (lt_of_not_ge h))

omit [Infinite K] in
/-- The finite coefficient sum recovers the homogeneous scaling expression
at every nonzero scalar, including negative degrees. -/
theorem symmetricTorusEvaluation_finiteLaurentCoefficientSum_scale
    (S : LaurentSeries (symmetricTorusSubalgebra σ K))
    (hS : S.support.Finite)
    (hhom : ∀ d, IsSymmetricTorusHomogeneous σ K (S.coeff d) d)
    (x : σ → Kˣ) (c : Kˣ) :
    symmetricTorusEvaluation σ K (fun i => c * x i)
        (finiteLaurentCoefficientSum S hS) =
      ∑ d ∈ hS.toFinset,
        (c : K) ^ d * (S.map (symmetricTorusEvaluation σ K x)).coeff d := by
  classical
  simp only [finiteLaurentCoefficientSum, map_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [← symmetricTorusEvaluation_scale, hhom d c, map_mul, AlgHom.commutes]
  rfl

end Algebra

section Model

open MeasureTheory Langlands.GeneralLinear Langlands.Whittaker
open Langlands.HarmonicAnalysis Langlands.RankinSelberg
open Langlands.QuotientIntegration

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
variable (w : (coefficientModel π ℓ).toSubmodule) (P : Polynomial ℂ)

/-- The product of the actual model series and the actual coordinate
denominator. Its definition does not assert that denominators are cleared. -/
def corankOneModelDenominatorProduct :
    LaurentSeries (symmetricTorusSubalgebra (Fin (n + 1)) ℂ) :=
  corankOneModelLaurentSeries h π hπ ℓ w *
    finitePolynomialLaurentSeries
      (A := symmetricTorusSubalgebra (Fin (n + 1)) ℂ)
      (coordinateDenominatorPolynomial (Fin (n + 1)) ℂ P)

theorem corankOneModelDenominatorProduct_coeff (d : ℤ) :
    (corankOneModelDenominatorProduct h π hπ ℓ w P).coeff d =
      ∑ m ∈ (coordinateDenominatorPolynomial (Fin (n + 1)) ℂ P).support,
        degreeCorankOneModelCoefficient h π hπ ℓ w (d - (m : ℤ)) *
          coordinateDenominatorCoefficient (Fin (n + 1)) ℂ P m := by
  simp only [corankOneModelDenominatorProduct, mul_finitePolynomialLaurentSeries_coeff,
    corankOneModelLaurentSeries_coeff, coordinateDenominatorPolynomial_coeff]

theorem corankOneModelDenominatorProduct_coeff_isHomogeneous (d : ℤ) :
    IsSymmetricTorusHomogeneous (Fin (n + 1)) ℂ
      ((corankOneModelDenominatorProduct h π hπ ℓ w P).coeff d) d :=
  mul_finitePolynomialLaurentSeries_coeff_isHomogeneous _ _
    (corankOneModelLaurentSeries_coeff_isHomogeneous h π hπ ℓ w)
    (coordinateDenominatorPolynomial_coeff_isHomogeneous (Fin (n + 1)) ℂ P) d

/-- One lower bound works for every scalar polynomial multiplier. -/
theorem corankOneModelDenominatorProduct_coeff_eq_zero_below :
    ∃ d₀ : ℤ, ∀ (P : Polynomial ℂ) (d : ℤ), d < d₀ →
      (corankOneModelDenominatorProduct h π hπ ℓ w P).coeff d = 0 := by
  obtain ⟨d₀, hd₀⟩ := degreeCorankOneModelCoefficient_eq_zero_below h π hπ ℓ w
  exact ⟨d₀, fun P => mul_finitePolynomialLaurentSeries_coeff_eq_zero_below
    (corankOneModelLaurentSeries h π hπ ℓ w) _ d₀ hd₀⟩

/-- Exact specialization of the product into scalar formal Laurent series. -/
theorem corankOneModelDenominatorProduct_specialize (x : Fin (n + 1) → ℂˣ) :
    (corankOneModelDenominatorProduct h π hπ ℓ w P).map
        (symmetricTorusEvaluation (Fin (n + 1)) ℂ x) =
      specializedCorankOneModelLaurentSeries h π hπ ℓ w x *
        finitePolynomialLaurentSeries
          (∏ i, P.comp (Polynomial.C (x i : ℂ) * Polynomial.X)) := by
  unfold corankOneModelDenominatorProduct
  change (corankOneModelLaurentSeries h π hπ ℓ w *
    finitePolynomialLaurentSeries
      (A := symmetricTorusSubalgebra (Fin (n + 1)) ℂ)
      (coordinateDenominatorPolynomial (Fin (n + 1)) ℂ P)).map
    (symmetricTorusEvaluation (Fin (n + 1)) ℂ x).toRingHom = _
  rw [mul_finitePolynomialLaurentSeries_map,
    coordinateDenominatorPolynomial_specialize]
  rfl

/-- Each specialized convolution coefficient is a finite linear combination
of actual scalar degree integrals. -/
theorem corankOneModelDenominatorProduct_specialized_coeff
    (x : Fin (n + 1) → ℂˣ) (d : ℤ) :
    ((corankOneModelDenominatorProduct h π hπ ℓ w P).map
      (symmetricTorusEvaluation (Fin (n + 1)) ℂ x)).coeff d =
      ∑ m ∈ (coordinateDenominatorPolynomial (Fin (n + 1)) ℂ P).support,
        (∫ t, (if sphericalQuotientDegree h.uniformizer t = d - (m : ℤ) then
          corankOneIntegrand ψ abv w.val
            (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) 0 t
          else 0) ∂μ) *
        symmetricTorusEvaluation (Fin (n + 1)) ℂ x
          (coordinateDenominatorCoefficient (Fin (n + 1)) ℂ P m) := by
  change symmetricTorusEvaluation (Fin (n + 1)) ℂ x
    ((corankOneModelDenominatorProduct h π hπ ℓ w P).coeff d) = _
  rw [corankOneModelDenominatorProduct_coeff, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [map_mul, symmetricTorusEvaluation_degreeCorankOneModelCoefficient]

/-- A uniform scalar upper bound, once proved, combines with the actual lower
bound to give finite support over the symmetric Laurent algebra. -/
theorem corankOneModelDenominatorProduct_support_finite
    (B : ℤ) (hhi : ∀ (x : Fin (n + 1) → ℂˣ) (d : ℤ), B < d →
      ((corankOneModelDenominatorProduct h π hπ ℓ w P).map
        (symmetricTorusEvaluation (Fin (n + 1)) ℂ x)).coeff d = 0) :
    (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite := by
  obtain ⟨d₀, hd₀⟩ := corankOneModelDenominatorProduct_coeff_eq_zero_below h π hπ ℓ w
  exact symmetricTorusLaurentSeries_support_finite_of_specialized_upper_bound
    (Fin (n + 1)) ℂ _ d₀ B (hd₀ P) hhi

end Model

end Langlands.Conductor
