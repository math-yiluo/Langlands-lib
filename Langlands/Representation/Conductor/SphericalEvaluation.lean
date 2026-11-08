import Langlands.Representation.Conductor.SphericalRational

/-! # Evaluation of finite spherical Laurent numerators -/

noncomputable section

namespace Langlands.Conductor

open scoped BigOperators

universe uA uK uσ uF uV

section RationalEvaluation

variable {K : Type uK} [Field K] {c : K}

private theorem denominator_eval_ne_zero_of_dvd {r : RatFunc K} {Q : Polynomial K}
    (hdiv : r.denom ∣ Q) (hQ : Q.eval₂ (RingHom.id K) c ≠ 0) :
    r.denom.eval₂ (RingHom.id K) c ≠ 0 := by
  intro hz
  exact hQ (Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hdiv hz)

private theorem denominator_add_eval_ne_zero {r t : RatFunc K}
    (hr : r.denom.eval₂ (RingHom.id K) c ≠ 0)
    (ht : t.denom.eval₂ (RingHom.id K) c ≠ 0) :
    (r + t).denom.eval₂ (RingHom.id K) c ≠ 0 := by
  apply denominator_eval_ne_zero_of_dvd (RatFunc.denom_add_dvd r t)
  simpa only [Polynomial.eval₂_mul] using mul_ne_zero hr ht

private theorem denominator_mul_eval_ne_zero {r t : RatFunc K}
    (hr : r.denom.eval₂ (RingHom.id K) c ≠ 0)
    (ht : t.denom.eval₂ (RingHom.id K) c ≠ 0) :
    (r * t).denom.eval₂ (RingHom.id K) c ≠ 0 := by
  apply denominator_eval_ne_zero_of_dvd (RatFunc.denom_mul_dvd r t)
  simpa only [Polynomial.eval₂_mul] using mul_ne_zero hr ht

private theorem denominator_sum_eval_ne_zero {ι : Type*}
    (s : Finset ι) (r : ι → RatFunc K)
    (hr : ∀ i ∈ s, (r i).denom.eval₂ (RingHom.id K) c ≠ 0) :
    (∑ i ∈ s, r i).denom.eval₂ (RingHom.id K) c ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact denominator_add_eval_ne_zero (hr i (Finset.mem_insert_self i s))
      (ih (fun j hj => hr j (Finset.mem_insert_of_mem hj)))

private theorem rationalFunction_eval_sum {ι : Type*}
    (s : Finset ι) (r : ι → RatFunc K)
    (hr : ∀ i ∈ s, (r i).denom.eval₂ (RingHom.id K) c ≠ 0) :
    RatFunc.eval (RingHom.id K) c (∑ i ∈ s, r i) =
      ∑ i ∈ s, RatFunc.eval (RingHom.id K) c (r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      RatFunc.eval_add (RingHom.id K) c (hr i (Finset.mem_insert_self i s))
        (denominator_sum_eval_ne_zero s r
          (fun j hj => hr j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hr j (Finset.mem_insert_of_mem hj))]

/-- An integer power of the rational variable has no pole away from zero. -/
theorem rationalXPow_denom_eval_ne_zero (hc : c ≠ 0) (d : ℤ) :
    (RatFunc.X ^ d : RatFunc K).denom.eval₂ (RingHom.id K) c ≠ 0 := by
  cases d with
  | ofNat n =>
    have hp : (RatFunc.X ^ n : RatFunc K) =
        algebraMap (Polynomial K) (RatFunc K) (Polynomial.X ^ n) := by simp
    rw [Int.ofNat_eq_natCast, zpow_natCast, hp, RatFunc.denom_algebraMap]
    simp
  | negSucc n =>
    rw [zpow_negSucc]
    apply denominator_eval_ne_zero_of_dvd
      (RatFunc.denom_inv_dvd (pow_ne_zero (n + 1) RatFunc.X_ne_zero))
    rw [← RatFunc.algebraMap_X, ← map_pow, RatFunc.num_algebraMap]
    simpa using pow_ne_zero (n + 1) hc

/-- Evaluating an integer power of the rational variable gives the same
integer power of any nonzero scalar. -/
theorem rationalXPow_eval (hc : c ≠ 0) (d : ℤ) :
    RatFunc.eval (RingHom.id K) c (RatFunc.X ^ d) = c ^ d := by
  cases d with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast,
      ← RatFunc.algebraMap_X, ← map_pow, RatFunc.eval_algebraMap]
    simp
  | negSucc n =>
    rw [zpow_negSucc, zpow_negSucc]
    have hp : (RatFunc.X ^ (n + 1) : RatFunc K).denom.eval₂ (RingHom.id K) c ≠ 0 := by
      simpa only [zpow_natCast] using rationalXPow_denom_eval_ne_zero hc (n + 1 : ℕ)
    have hi : ((RatFunc.X ^ (n + 1))⁻¹ : RatFunc K).denom.eval₂
        (RingHom.id K) c ≠ 0 := by
      simpa only [zpow_negSucc] using rationalXPow_denom_eval_ne_zero hc (.negSucc n)
    have he := RatFunc.eval_mul (RingHom.id K) c hp hi
    rw [mul_inv_cancel₀ (pow_ne_zero (n + 1) RatFunc.X_ne_zero), RatFunc.eval_one,
      ← RatFunc.algebraMap_X, ← map_pow, RatFunc.eval_algebraMap] at he
    simpa using (inv_eq_of_mul_eq_one_right he.symm).symm

/-- A rational Laurent monomial has no pole at a nonzero scalar. -/
theorem rationalMonomial_denom_eval_ne_zero (hc : c ≠ 0) (a : K) (d : ℤ) :
    (RatFunc.C a * RatFunc.X ^ d).denom.eval₂ (RingHom.id K) c ≠ 0 := by
  apply denominator_mul_eval_ne_zero
  · simp
  · exact rationalXPow_denom_eval_ne_zero hc d

/-- Evaluation of a rational Laurent monomial away from zero. -/
theorem rationalMonomial_eval (hc : c ≠ 0) (a : K) (d : ℤ) :
    RatFunc.eval (RingHom.id K) c (RatFunc.C a * RatFunc.X ^ d) = a * c ^ d := by
  rw [RatFunc.eval_mul (RingHom.id K) c (by simp) (rationalXPow_denom_eval_ne_zero hc d),
    RatFunc.eval_C, RingHom.id_apply, rationalXPow_eval hc]

variable {A : Type uA} [CommRing A]

/-- The rational function constructed from finite Laurent support has no
pole at a nonzero scalar, even if some original coefficients specialize to zero. -/
theorem finiteLaurentRationalFunction_denom_eval_ne_zero
    (S : LaurentSeries A) (hS : S.support.Finite) (f : A →+* K) (hc : c ≠ 0) :
    (finiteLaurentRationalFunction S hS f).denom.eval₂ (RingHom.id K) c ≠ 0 := by
  apply denominator_sum_eval_ne_zero
  intro d _
  exact rationalMonomial_denom_eval_ne_zero hc _ d

/-- Evaluation of the rational function is the finite Laurent sum at every
nonzero scalar. No infinite series is evaluated. -/
theorem finiteLaurentRationalFunction_eval
    (S : LaurentSeries A) (hS : S.support.Finite) (f : A →+* K) (hc : c ≠ 0) :
    RatFunc.eval (RingHom.id K) c (finiteLaurentRationalFunction S hS f) =
      ∑ d ∈ hS.toFinset, f (S.coeff d) * c ^ d := by
  classical
  rw [finiteLaurentRationalFunction,
    rationalFunction_eval_sum _ _ (fun d _ => rationalMonomial_denom_eval_ne_zero hc _ d)]
  apply Finset.sum_congr rfl
  intro d _
  exact rationalMonomial_eval hc _ d

/-- At one, evaluation is the image of the finite coefficient sum. -/
theorem finiteLaurentRationalFunction_eval_one
    (S : LaurentSeries A) (hS : S.support.Finite) (f : A →+* K) :
    RatFunc.eval (RingHom.id K) 1 (finiteLaurentRationalFunction S hS f) =
      f (finiteLaurentCoefficientSum S hS) := by
  rw [finiteLaurentRationalFunction_eval S hS f one_ne_zero]
  simp [finiteLaurentCoefficientSum]

end RationalEvaluation

section HomogeneousEvaluation

variable (σ : Type uσ) (K : Type uK) [Fintype σ] [Field K]

/-- For homogeneous coefficients, rational evaluation equals evaluation of
the finite coefficient sum after scaling the tuple. -/
theorem finiteLaurentRationalFunction_eval_eq_symmetricTorusEvaluation_scale
    (S : LaurentSeries (symmetricTorusSubalgebra σ K)) (hS : S.support.Finite)
    (hhom : ∀ d, IsSymmetricTorusHomogeneous σ K (S.coeff d) d)
    (x : σ → Kˣ) (c : Kˣ) :
    RatFunc.eval (RingHom.id K) (c : K)
        (finiteLaurentRationalFunction S hS (symmetricTorusEvaluation σ K x).toRingHom) =
      symmetricTorusEvaluation σ K (fun i => c * x i)
        (finiteLaurentCoefficientSum S hS) := by
  rw [finiteLaurentRationalFunction_eval S hS _ (Units.ne_zero c),
    symmetricTorusEvaluation_finiteLaurentCoefficientSum_scale σ K S hS hhom x c]
  apply Finset.sum_congr rfl
  intro d _
  exact mul_comm _ _

end HomogeneousEvaluation

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

/-- The symmetric Laurent numerator of the actual model product, obtained
by summing its actual coefficients under an explicit finite-support hypothesis. -/
def corankOneModelNumerator
    (hfinite : (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite) :
    symmetricTorusSubalgebra (Fin (n + 1)) ℂ :=
  finiteLaurentCoefficientSum (corankOneModelDenominatorProduct h π hπ ℓ w P) hfinite

/-- Evaluation of the numerator is the finite sum of the specialized actual
convolution coefficients. -/
theorem corankOneModelNumerator_evaluation
    (hfinite : (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite)
    (x : Fin (n + 1) → ℂˣ) :
    symmetricTorusEvaluation (Fin (n + 1)) ℂ x
        (corankOneModelNumerator h π hπ ℓ w P hfinite) =
      ∑ d ∈ hfinite.toFinset,
        ((corankOneModelDenominatorProduct h π hπ ℓ w P).map
          (symmetricTorusEvaluation (Fin (n + 1)) ℂ x)).coeff d := by
  simp only [corankOneModelNumerator, finiteLaurentCoefficientSum, map_sum]
  rfl

/-- The actual scalar rational numerator has no pole away from zero. -/
theorem corankOneModelRationalNumerator_denom_eval_ne_zero
    (hfinite : (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite)
    (x : Fin (n + 1) → ℂˣ) {c : ℂ} (hc : c ≠ 0) :
    (corankOneModelRationalNumerator h π hπ ℓ w P hfinite x).denom.eval₂
        (RingHom.id ℂ) c ≠ 0 :=
  finiteLaurentRationalFunction_denom_eval_ne_zero _ hfinite _ hc

/-- Evaluating the actual scalar rational numerator at a nonzero scalar
agrees with evaluating the symmetric numerator at the scaled tuple. -/
theorem corankOneModelRationalNumerator_eval
    (hfinite : (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite)
    (x : Fin (n + 1) → ℂˣ) (c : ℂˣ) :
    RatFunc.eval (RingHom.id ℂ) (c : ℂ)
        (corankOneModelRationalNumerator h π hπ ℓ w P hfinite x) =
      symmetricTorusEvaluation (Fin (n + 1)) ℂ (fun i => c * x i)
        (corankOneModelNumerator h π hπ ℓ w P hfinite) :=
  finiteLaurentRationalFunction_eval_eq_symmetricTorusEvaluation_scale
    (Fin (n + 1)) ℂ _ hfinite
      (corankOneModelDenominatorProduct_coeff_isHomogeneous h π hπ ℓ w P) x c

/-- At one, the actual scalar rational numerator specializes the symmetric
numerator without any scaling. -/
theorem corankOneModelRationalNumerator_eval_one
    (hfinite : (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite)
    (x : Fin (n + 1) → ℂˣ) :
    RatFunc.eval (RingHom.id ℂ) 1
        (corankOneModelRationalNumerator h π hπ ℓ w P hfinite x) =
      symmetricTorusEvaluation (Fin (n + 1)) ℂ x
        (corankOneModelNumerator h π hπ ℓ w P hfinite) :=
  finiteLaurentRationalFunction_eval_one _ hfinite _

end Model

end Langlands.Conductor
