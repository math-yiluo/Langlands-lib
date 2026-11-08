import Langlands.Representation.Conductor.SphericalProduct
import Mathlib.RingTheory.LaurentSeries

/-! # Rational functions associated to finite spherical Laurent products -/

noncomputable section

namespace Langlands.Conductor

open scoped BigOperators RatFunc

universe uA uK uF uV

section PolynomialEmbedding

variable {A : Type uA} [CommRing A]

/-- The finite-sum embedding agrees with the canonical polynomial algebra map. -/
theorem finitePolynomialLaurentSeries_eq_algebraMap (P : Polynomial A) :
    finitePolynomialLaurentSeries P = algebraMap (Polynomial A) (LaurentSeries A) P := by
  rw [Polynomial.algebraMap_hahnSeries_apply]
  change finitePolynomialLaurentSeries P = ((P : PowerSeries A) : LaurentSeries A)
  apply HahnSeries.ext
  funext d
  cases d <;> simp [PowerSeries.coeff_coe]

theorem finitePolynomialLaurentSeries_ne_zero {P : Polynomial A} (hP : P ≠ 0) :
    finitePolynomialLaurentSeries P ≠ 0 := by
  rw [finitePolynomialLaurentSeries_eq_algebraMap]
  simpa only [map_zero] using (Polynomial.algebraMap_hahnSeries_injective ℤ).ne hP

end PolynomialEmbedding

section FiniteRationalFunction

variable {A : Type uA} [CommRing A] {K : Type uK} [Field K]

/-- The rational Laurent polynomial obtained by mapping a finite series'
actual coefficients to a field. Integer exponents may be negative. -/
def finiteLaurentRationalFunction (S : LaurentSeries A) (hS : S.support.Finite)
    (f : A →+* K) : RatFunc K :=
  ∑ d ∈ hS.toFinset, RatFunc.C (f (S.coeff d)) * RatFunc.X ^ d

/-- Expansion of a rational monomial gives the corresponding Hahn monomial. -/
theorem rationalMonomial_laurentExpansion (a : K) (d : ℤ) :
    algebraMap (RatFunc K) (LaurentSeries K) (RatFunc.C a * RatFunc.X ^ d) =
      HahnSeries.single d a := by
  rw [map_mul, map_zpow₀]
  have hC : algebraMap (RatFunc K) (LaurentSeries K) (RatFunc.C a) =
      HahnSeries.C a := by
    change algebraMap (RatFunc K) (LaurentSeries K)
      (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a)) = _
    rw [← IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) (LaurentSeries K)]
    simp
  rw [hC, RatFunc.coe_X, ← RatFunc.single_zpow]
  simp

/-- The rational Laurent polynomial expands to the coefficient specialization
of the original finite Laurent series. -/
theorem finiteLaurentRationalFunction_laurentExpansion
    (S : LaurentSeries A) (hS : S.support.Finite) (f : A →+* K) :
    algebraMap (RatFunc K) (LaurentSeries K) (finiteLaurentRationalFunction S hS f) =
      S.map f := by
  classical
  simp only [finiteLaurentRationalFunction, map_sum, rationalMonomial_laurentExpansion]
  apply HahnSeries.ext
  funext d
  rw [HahnSeries.coeff_sum]
  change (∑ e ∈ hS.toFinset, (HahnSeries.single e (f (S.coeff e))).coeff d) =
    f (S.coeff d)
  trans (HahnSeries.single d (f (S.coeff d))).coeff d
  · apply Finset.sum_eq_single d
    · intro e _ hed
      exact HahnSeries.coeff_single_of_ne hed.symm
    · intro hd
      have hz : S.coeff d = 0 := by
        simpa only [Set.Finite.mem_toFinset, HahnSeries.mem_support, not_not] using hd
      simp [hz]
  · exact HahnSeries.coeff_single_same d (f (S.coeff d))

end FiniteRationalFunction

section EssentialFactor

open Langlands.RankinSelberg

/-- The normalized coordinate product has constant coefficient one. -/
theorem specializedCoordinateDenominator_coeff_zero
    {m : ℕ} (P : Polynomial ℂ) (hP : P.coeff 0 = 1) (x : Fin m → ℂˣ) :
    (∏ i, P.comp (Polynomial.C (x i : ℂ) * Polynomial.X)).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, mul_zero, ← Polynomial.coeff_zero_eq_eval_zero, hP,
    Finset.prod_const_one]

theorem specializedCoordinateDenominator_ne_zero
    {m : ℕ} (P : Polynomial ℂ) (hP : P.coeff 0 = 1) (x : Fin m → ℂˣ) :
    (∏ i, P.comp (Polynomial.C (x i : ℂ) * Polynomial.X)) ≠ 0 := by
  intro hz
  have h0 := specializedCoordinateDenominator_coeff_zero P hP x
  rw [hz, Polynomial.coeff_zero] at h0
  exact zero_ne_one h0

/-- The existing essential factor expands to the reciprocal of the actual
specialized finite coordinate denominator. -/
theorem essentialFactor_laurentExpansion
    {m : ℕ} (P : Polynomial ℂ) (x : Fin m → ℂˣ) :
    algebraMap RationalFunctions (LaurentSeries ℂ) (essentialFactor P x) =
      (finitePolynomialLaurentSeries
        (∏ i, P.comp (Polynomial.C (x i : ℂ) * Polynomial.X)))⁻¹ := by
  rw [essentialFactor_eq, map_inv₀,
    ← IsScalarTower.algebraMap_apply (Polynomial ℂ) RationalFunctions (LaurentSeries ℂ),
    ← finitePolynomialLaurentSeries_eq_algebraMap]

/-- Normalization guarantees that the formal denominator is nonzero. -/
theorem essentialFactor_laurentExpansion_mul_denominator
    {m : ℕ} (P : Polynomial ℂ) (hP : P.coeff 0 = 1) (x : Fin m → ℂˣ) :
    algebraMap RationalFunctions (LaurentSeries ℂ) (essentialFactor P x) *
      finitePolynomialLaurentSeries
        (∏ i, P.comp (Polynomial.C (x i : ℂ) * Polynomial.X)) = 1 := by
  rw [essentialFactor_laurentExpansion]
  exact inv_mul_cancel₀ (finitePolynomialLaurentSeries_ne_zero
    (specializedCoordinateDenominator_ne_zero P hP x))

end EssentialFactor

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

/-- The rational Laurent numerator formed from the actual finite-support
denominator product. Finiteness is an explicit proof input. -/
def corankOneModelRationalNumerator
    (hfinite : (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite)
    (x : Fin (n + 1) → ℂˣ) : RationalFunctions :=
  finiteLaurentRationalFunction (corankOneModelDenominatorProduct h π hπ ℓ w P)
    hfinite (symmetricTorusEvaluation (Fin (n + 1)) ℂ x).toRingHom

/-- Its expansion is the actual specialized model series times the
specialized coordinate denominator. -/
theorem corankOneModelRationalNumerator_laurentExpansion
    (hfinite : (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite)
    (x : Fin (n + 1) → ℂˣ) :
    algebraMap RationalFunctions (LaurentSeries ℂ)
        (corankOneModelRationalNumerator h π hπ ℓ w P hfinite x) =
      specializedCorankOneModelLaurentSeries h π hπ ℓ w x *
        finitePolynomialLaurentSeries
          (∏ i, P.comp (Polynomial.C (x i : ℂ) * Polynomial.X)) := by
  rw [corankOneModelRationalNumerator,
    finiteLaurentRationalFunction_laurentExpansion]
  exact corankOneModelDenominatorProduct_specialize h π hπ ℓ w P x

/-- Finite support and constant-term normalization give a formal rational
expression for the actual specialized model series. -/
theorem specializedCorankOneModelLaurentSeries_eq_laurentExpansion
    (hP : P.coeff 0 = 1)
    (hfinite : (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite)
    (x : Fin (n + 1) → ℂˣ) :
    specializedCorankOneModelLaurentSeries h π hπ ℓ w x =
      algebraMap RationalFunctions (LaurentSeries ℂ)
        (corankOneModelRationalNumerator h π hπ ℓ w P hfinite x *
          essentialFactor P x) := by
  rw [map_mul, corankOneModelRationalNumerator_laurentExpansion,
    essentialFactor_laurentExpansion, mul_assoc,
    mul_inv_cancel₀ (finitePolynomialLaurentSeries_ne_zero
      (specializedCoordinateDenominator_ne_zero P hP x)), mul_one]

end Model

end Langlands.Conductor
