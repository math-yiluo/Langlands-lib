import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentAlgebra
import Langlands.Representation.RankinSelberg.LaurentEvaluation

/-!
# Reflection of the polynomial-cleared small functional equation

Derived finite Laurent algebra for the JPSS first-block proof. Reflection is
performed on finite cleared polynomials and then transported to bilateral
coefficients. No polynomial is cancelled on the bilateral module.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockFirstBlockLaurent

open MeasureTheory LaurentPolynomial HarmonicAnalysis
open HarmonicAnalysis.BilateralLaurentSeries

private def reflectionMonomials (q : ℕ) (hq : 0 < q) :
    Multiplicative ℤ →* LaurentPolynomial ℂ where
  toFun k := LaurentPolynomial.C ((q : ℂ) ^ (-k.toAdd)) *
    LaurentPolynomial.T (-k.toAdd)
  map_one' := by simp
  map_mul' j k := by
    have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    change LaurentPolynomial.C ((q : ℂ) ^ (-(j.toAdd + k.toAdd))) *
      LaurentPolynomial.T (-(j.toAdd + k.toAdd)) = _
    rw [neg_add]
    rw [zpow_add₀ hq0, LaurentPolynomial.T_add, map_mul]
    ring

/-- Reciprocal spectral substitution `X ↦ q⁻¹ X⁻¹` on finite Laurent polynomials. -/
def reflectLaurent (q : ℕ) (hq : 0 < q) :
    LaurentPolynomial ℂ →ₐ[ℂ] LaurentPolynomial ℂ :=
  AddMonoidAlgebra.lift ℂ (LaurentPolynomial ℂ) ℤ (reflectionMonomials q hq)

theorem reflectLaurent_monomial (q : ℕ) (hq : 0 < q) (c : ℂ) (k : ℤ) :
    reflectLaurent q hq (LaurentPolynomial.C c * LaurentPolynomial.T k) =
      LaurentPolynomial.C (c * (q : ℂ) ^ (-k)) * LaurentPolynomial.T (-k) := by
  rw [reflectLaurent, ← LaurentPolynomial.single_eq_C_mul_T,
    AddMonoidAlgebra.lift_single]
  change c • (LaurentPolynomial.C ((q : ℂ) ^ (-k)) *
    LaurentPolynomial.T (-k)) = _
  rw [Algebra.smul_def, ← LaurentPolynomial.C_eq_algebraMap, ← mul_assoc, ← map_mul]

@[simp]
theorem reflectLaurent_C (q : ℕ) (hq : 0 < q) (c : ℂ) :
    reflectLaurent q hq (LaurentPolynomial.C c) = LaurentPolynomial.C c := by
  simpa using reflectLaurent_monomial q hq c 0

@[simp]
theorem reflectLaurent_T (q : ℕ) (hq : 0 < q) (k : ℤ) :
    reflectLaurent q hq (LaurentPolynomial.T k) =
      LaurentPolynomial.C ((q : ℂ) ^ (-k)) * LaurentPolynomial.T (-k) := by
  simpa using reflectLaurent_monomial q hq 1 k

/-- Reflection of an arbitrary bilateral coefficient function. -/
def reflectSeries (q : ℕ) (a : BilateralLaurentSeries) : BilateralLaurentSeries :=
  fun n => (q : ℂ) ^ n * a (-n)

@[simp]
theorem reflectSeries_apply (q : ℕ) (a : BilateralLaurentSeries) (n : ℤ) :
    reflectSeries q a n = (q : ℂ) ^ n * a (-n) := rfl

/-- Reflection intertwines finite Laurent convolution with spectral substitution. -/
theorem reflectSeries_laurent_smul (q : ℕ) (hq : 0 < q)
    (P : LaurentPolynomial ℂ) (a : BilateralLaurentSeries) :
    reflectSeries q (P • a) = reflectLaurent q hq P • reflectSeries q a := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ =>
    ext n
    simpa only [add_smul, map_add, add_apply, reflectSeries_apply, mul_add] using
      congrArg (fun b : BilateralLaurentSeries => b n) (congrArg₂ (· + ·) hP hQ)
  | C_mul_T k c =>
    ext n
    simp only [reflectLaurent_monomial, C_mul_T_smul_apply, reflectSeries_apply,
      sub_neg_eq_add]
    rw [show -(n + k) = -n - k by omega]
    have hp : (q : ℂ) ^ (-k) * (q : ℂ) ^ (n + k) = (q : ℂ) ^ n := by
      rw [← zpow_add₀ hq0]
      congr 1
      omega
    calc
      (q : ℂ) ^ n * (c * a (-n - k)) =
          c * ((q : ℂ) ^ (-k) * (q : ℂ) ^ (n + k)) * a (-n - k) := by rw [hp]; ring
      _ = _ := by ring

/-- The finite reflection agrees with the prescribed dual polynomial. -/
theorem reflectLaurent_toLaurent (q : ℕ) (hq : 0 < q) (P : Polynomial ℂ) :
    reflectLaurent q hq P.toLaurent = reflectedPolynomial q P := by
  rw [toLaurent_eq_sum, map_sum, reflectedPolynomial_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [reflectLaurent_monomial]
  simp only [zpow_neg, zpow_natCast, inv_pow]

/-- Reflection of finite coefficients is the embedding of the reflected polynomial. -/
theorem reflectSeries_ofLaurentPolynomial (q : ℕ) (hq : 0 < q)
    (P : LaurentPolynomial ℂ) :
    reflectSeries q (ofLaurentPolynomial P) =
      ofLaurentPolynomial (reflectLaurent q hq P) := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ =>
    ext n
    simpa only [map_add, add_apply, reflectSeries_apply, mul_add] using
      congrArg (fun a : BilateralLaurentSeries => a n) (congrArg₂ (· + ·) hP hQ)
  | C_mul_T k c =>
    ext n
    rw [reflectLaurent_monomial]
    by_cases hn : n = -k
    · subst n
      simp only [reflectSeries_apply, ofLaurentPolynomial_apply,
        ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
        Finsupp.single_apply, neg_neg]
      exact mul_comm _ _
    · have hnk : -n ≠ k := by omega
      simp only [reflectSeries_apply, ofLaurentPolynomial_apply,
        ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
        Finsupp.single_apply, hnk.symm, Ne.symm hn, ite_false, mul_zero]

/-- Finite reflection is evaluation at the reflected spectral parameter. -/
theorem laurentEval_reflectLaurent {q : ℕ} (hq : 0 < q) (s : ℂ)
    (P : LaurentPolynomial ℂ) :
    laurentEval (spectralUnit hq s) (reflectLaurent q hq P) =
      laurentEval (spectralUnit hq (1 - s)) P := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | C_mul_T k c =>
    rw [reflectLaurent_monomial]
    simp only [map_mul, laurentEval_C, laurentEval_T,
      coe_spectralUnit, spectralPoint_sub_one_sub hq, mul_zpow, inv_zpow, zpow_neg]
    ring

/-- Finite Laurent polynomials are determined by any infinite real spectral set. -/
theorem laurent_eq_of_infinite_spectral_eval_eq {q : ℕ} (hq : 1 < q)
    {P Q : LaurentPolynomial ℂ} (S : Set ℝ) (hS : S.Infinite)
    (h : ∀ t ∈ S,
      laurentEval (spectralUnit (Nat.zero_lt_one.trans hq) (t : ℂ)) P =
        laurentEval (spectralUnit (Nat.zero_lt_one.trans hq) (t : ℂ)) Q) : P = Q := by
  apply laurentToRatFunc_injective
  apply rationalFunction_eq_of_infinite_eval_eq _ _
    ((fun t : ℝ => spectralPoint q (t : ℂ)) '' S)
    (hS.image (spectralPoint_ofReal_injective hq).injOn)
  · rintro x ⟨t, ht, rfl⟩
    exact laurentToRatFunc_regular (spectralUnit (Nat.zero_lt_one.trans hq) (t : ℂ)) P
  · rintro x ⟨t, ht, rfl⟩
    exact laurentToRatFunc_regular (spectralUnit (Nat.zero_lt_one.trans hq) (t : ℂ)) Q
  · rintro x ⟨t, ht, rfl⟩
    simpa only [← coe_spectralUnit (Nat.zero_lt_one.trans hq) (t : ℂ),
      eval_laurentToRatFunc] using h t ht

/-- A normalized functional equation gives an identity of its finite Laurent lifts.
Only actual denominator nonvanishing is used when applying the scalar equation. -/
theorem normalizedFE_cleared_laurent_identity {q : ℕ} (hq : 1 < q)
    {P Pdual : Polynomial ℂ} {ζ c : ℂˣ} {e : ℕ} {d : ℤ}
    {R Rd : RationalFunctions} {L Ld : LaurentPolynomial ℂ}
    (hL : laurentToRatFunc L = algebraMap (Polynomial ℂ) RationalFunctions P * R)
    (hLd : laurentToRatFunc Ld = algebraMap (Polynomial ℂ) RationalFunctions Pdual * Rd)
    (hFE : NormalizedFunctionalEquation q P Pdual ζ c e d R Rd) :
    reflectLaurent q (Nat.zero_lt_one.trans hq) Ld =
      (LaurentPolynomial.C ((ζ : ℂ) ^ e * (c : ℂ)) * LaurentPolynomial.T d) * L := by
  let bad : Set ℝ :=
    {t | R.denom.eval (spectralPoint q (t : ℂ)) = 0} ∪
      {t | Rd.denom.eval (spectralPoint q (1 - (t : ℂ))) = 0}
  have hbad : bad.Finite :=
    (finite_spectralPoint_roots hq (RatFunc.denom_ne_zero R)).union
      (finite_reflected_spectralPoint_roots hq (RatFunc.denom_ne_zero Rd))
  apply laurent_eq_of_infinite_spectral_eval_eq hq badᶜ hbad.infinite_compl
  intro t ht
  simp only [bad, Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, not_or] at ht
  obtain ⟨hR, hRd⟩ := ht
  rw [laurentEval_reflectLaurent, map_mul, map_mul, laurentEval_C, laurentEval_T]
  rw [laurentEval_eq_of_laurentToRatFunc_eq _ hLd hRd,
    laurentEval_eq_of_laurentToRatFunc_eq _ hL hR]
  simpa only [coe_spectralUnit, epsilonMonomial, mul_assoc] using hFE (t : ℂ) hR hRd

/-- Once both right-half-plane series have been identified with their finite
cleared Laurent lifts, the normalized equation yields the reflected coefficient identity. -/
theorem normalizedFE_coefficient_identity_of_cleared {q : ℕ} (hq : 1 < q)
    {P Pdual : Polynomial ℂ} {ζ c : ℂˣ} {e : ℕ} {d : ℤ}
    {R Rd : RationalFunctions} {L Ld : LaurentPolynomial ℂ}
    (hL : laurentToRatFunc L = algebraMap (Polynomial ℂ) RationalFunctions P * R)
    (hLd : laurentToRatFunc Ld = algebraMap (Polynomial ℂ) RationalFunctions Pdual * Rd)
    (hFE : NormalizedFunctionalEquation q P Pdual ζ c e d R Rd)
    (a ad : BilateralLaurentSeries)
    (ha : P.toLaurent • a = ofLaurentPolynomial L)
    (had : Pdual.toLaurent • ad = ofLaurentPolynomial Ld) :
    reflectedPolynomial q Pdual • reflectSeries q ad =
      (LaurentPolynomial.C ((ζ : ℂ) ^ e * (c : ℂ)) *
        LaurentPolynomial.T d * P.toLaurent) • a := by
  rw [← reflectLaurent_toLaurent q (Nat.zero_lt_one.trans hq),
    ← reflectSeries_laurent_smul q (Nat.zero_lt_one.trans hq), had,
    reflectSeries_ofLaurentPolynomial q (Nat.zero_lt_one.trans hq),
    normalizedFE_cleared_laurent_identity hq hL hLd hFE, ofLaurentPolynomial_mul,
    ← ha, ← mul_smul]

section Integration

variable {A : Type*} [MeasurableSpace A] {μ : Measure A}
  {S U : A → BilateralLaurentSeries}

/-- Coefficient integrals respect almost-everywhere equality of series. -/
theorem coeffwiseIntegral_congr_ae (h : ∀ᵐ x ∂μ, S x = U x) :
    coeffwiseIntegral μ S = coeffwiseIntegral μ U := by
  ext n
  exact integral_congr_ae (h.mono fun x hx => congrArg (fun a : BilateralLaurentSeries => a n) hx)

/-- An almost-everywhere Laurent identity can be integrated coefficient by coefficient. -/
theorem integral_laurent_identity_ae (D E : LaurentPolynomial ℂ)
    (hS : CoeffwiseIntegrable S μ) (hU : CoeffwiseIntegrable U μ)
    (h : ∀ᵐ x ∂μ, D • S x = E • U x) :
    D • coeffwiseIntegral μ S = E • coeffwiseIntegral μ U := by
  rw [← coeffwiseIntegral_laurent_smul D hS,
    ← coeffwiseIntegral_laurent_smul E hU]
  exact coeffwiseIntegral_congr_ae h

end Integration

end Langlands.RankinSelberg.TwoBlockFirstBlockLaurent
