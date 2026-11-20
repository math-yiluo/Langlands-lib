import Langlands.Correspondence.AutomorphicGammaGerm
import Langlands.Representation.RankinSelberg.LaurentEvaluation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Evaluating the normalized p-adic zeta values -/

noncomputable section

set_option autoImplicit false

open Filter Polynomial Set Topology

namespace Langlands.RankinSelberg

private theorem normalizedLaurent_exists {values : Set RationalFunctions} {P : ℂ[X]}
    (h : IsNormalizedGenerator values P) (R : zetaSpan values) :
    ∃ a : LaurentCoefficients, laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * R :=
  h.clearsDenominators R.property

/-- Multiplication by the L-polynomial sends the zeta span to Laurent
polynomials. This map takes the Laurent polynomial corresponding to each value. -/
def IsNormalizedGenerator.normalizedLaurent {values : Set RationalFunctions} {P : ℂ[X]}
    (h : IsNormalizedGenerator values P) : zetaSpan values →ₗ[LaurentCoefficients] LaurentCoefficients where
  toFun R := (normalizedLaurent_exists h R).choose
  map_add' R S := laurentToRatFunc_injective <| by
    rw [map_add, (normalizedLaurent_exists h (R + S)).choose_spec,
      (normalizedLaurent_exists h R).choose_spec, (normalizedLaurent_exists h S).choose_spec]
    change _ * ((R : RationalFunctions) + S) = _
    exact mul_add ..
  map_smul' a R := laurentToRatFunc_injective <| by
    change laurentToRatFunc (normalizedLaurent_exists h (a • R)).choose =
      laurentToRatFunc (a * (normalizedLaurent_exists h R).choose)
    rw [map_mul, (normalizedLaurent_exists h (a • R)).choose_spec,
      (normalizedLaurent_exists h R).choose_spec]
    change _ * (a • (R : RationalFunctions)) = _
    rw [Algebra.smul_def, algebraMap_laurent, mul_left_comm]

/-- The normalized Laurent polynomial clears the denominator in the rational field. -/
theorem IsNormalizedGenerator.normalizedLaurent_spec {values : Set RationalFunctions} {P : ℂ[X]}
    (h : IsNormalizedGenerator values P) (R : zetaSpan values) :
    laurentToRatFunc (h.normalizedLaurent R) = algebraMap ℂ[X] RationalFunctions P * R :=
  (normalizedLaurent_exists h R).choose_spec

/-- The normalized values have no common zero at a nonzero value of the spectral
variable. Otherwise the entire zeta span would normalize to zero there, although
it contains the reciprocal generator, which normalizes to one. -/
theorem IsNormalizedGenerator.exists_laurentEval_normalizedLaurent_ne_zero
    {values : Set RationalFunctions} {P : ℂ[X]}
    (h : IsNormalizedGenerator values P) (z : ℂˣ) :
    ∃ R : values, laurentEval z (h.normalizedLaurent ⟨R, mem_zetaSpan R.property⟩) ≠ 0 := by
  by_contra! hzero
  have hAll (R : RationalFunctions) (hR : R ∈ zetaSpan values) :
      laurentEval z (h.normalizedLaurent ⟨R, hR⟩) = 0 := by
    refine Submodule.span_induction (p := fun R hR =>
      laurentEval z (h.normalizedLaurent ⟨R, hR⟩) = 0) ?_ ?_ ?_ ?_ hR
    · exact fun R hR => hzero ⟨R, hR⟩
    · change laurentEval z (h.normalizedLaurent 0) = 0
      simp
    · intro R S hR hS hR' hS'
      change laurentEval z (h.normalizedLaurent (⟨R, hR⟩ + ⟨S, hS⟩)) = 0
      simp only [map_add, hR', hS', add_zero]
    · intro a R hR hR'
      change laurentEval z (h.normalizedLaurent (a • ⟨R, hR⟩)) = 0
      simp only [map_smul, smul_eq_mul, map_mul, hR', mul_zero]
  let aP := algebraMap ℂ[X] RationalFunctions P
  have hInv : aP⁻¹ ∈ zetaSpan values := (isNormalizedGenerator_iff values P).mp h |>.2.2
  have hOne : h.normalizedLaurent ⟨aP⁻¹, hInv⟩ = 1 := by
    apply laurentToRatFunc_injective
    rw [h.normalizedLaurent_spec, map_one]
    exact mul_inv_cancel₀ (RatFunc.algebraMap_ne_zero h.polynomial_ne_zero)
  have hbad := hAll aP⁻¹ hInv
  rw [hOne, map_one] at hbad
  exact one_ne_zero hbad

/-- Laurent evaluation at the spectral point is entire for `q > 1`. -/
theorem analyticAt_laurentEval_spectralUnit {q : ℕ} (hq : 1 < q)
    (a : LaurentCoefficients) (s : ℂ) :
    AnalyticAt ℂ (fun z => laurentEval (spectralUnit (Nat.zero_lt_one.trans hq) z) a) s := by
  induction a using LaurentPolynomial.induction_on_mul_T with
  | mul_T P n =>
    have hP := analyticAt_polynomial_spectralPoint q hq P s
    have hX : AnalyticAt ℂ (spectralPoint q) s := by
      simpa using analyticAt_polynomial_spectralPoint q hq X s
    have hpow := hX.fun_zpow (n := -(n : ℤ)) (spectralPoint_ne_zero_of_pos (Nat.zero_lt_one.trans hq) s)
    simpa only [map_mul, laurentEval_toLaurent, laurentEval_T, coe_spectralUnit] using hP.fun_mul hpow

/-- A polynomial with nonzero constant coefficient has no spectral zero on some
right half-plane. The spectral point tends uniformly to zero as the real part grows. -/
theorem exists_rightHalfPlane_eval_spectralPoint_ne_zero {q : ℕ} (hq : 1 < q)
    {P : ℂ[X]} (hP : P.eval 0 ≠ 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → P.eval (spectralPoint q s) ≠ 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (P.continuous.continuousAt.eventually_ne hP)
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hlim : Tendsto (fun t : ℝ => (q : ℝ) ^ (-t)) atTop (𝓝 0) :=
    (tendsto_rpow_atBot_of_base_gt_one (q : ℝ) hqR).comp tendsto_neg_atTop_atBot
  obtain ⟨σ, hσ⟩ := eventually_atTop.mp (hlim.eventually_lt_const hε)
  refine ⟨σ, fun s hs => hball ?_⟩
  simpa only [Metric.mem_ball, dist_zero_right, spectralPoint,
    Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_one.trans hq), Complex.neg_re] using hσ s.re hs.le

/-- Evaluating the cleared Laurent polynomial returns the normalized test on an
initial half-plane. The equality also expresses the test as this entire factor
multiplied by the finite local L-factor. -/
theorem IsNormalizedGenerator.exists_eq_spectralNormalization_mul_L
    {values : Set RationalFunctions} {P : ℂ[X]} (h : IsNormalizedGenerator values P)
    {q : ℕ} (hq : 1 < q) (R : zetaSpan values) {f : ℂ → ℂ}
    (hf : HasRationalContinuation q f R) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      f s = laurentEval (spectralUnit (Nat.zero_lt_one.trans hq) s) (h.normalizedLaurent R) *
        (P.eval (spectralPoint q s))⁻¹ := by
  obtain ⟨a, ha⟩ := hf
  have hP : P.eval 0 ≠ 0 := by
    rw [← coeff_zero_eq_eval_zero, h.1]
    exact one_ne_zero
  obtain ⟨b, hb⟩ := exists_rightHalfPlane_eval_spectralPoint_ne_zero hq hP
  refine ⟨max a b, fun s hs => ?_⟩
  obtain ⟨hreg, heval⟩ := ha s (lt_of_le_of_lt (le_max_left a b) hs)
  have hnonzero := hb s (lt_of_le_of_lt (le_max_right a b) hs)
  rw [laurentEval_eq_of_laurentToRatFunc_eq _ (h.normalizedLaurent_spec R) hreg, coe_spectralUnit, ← heval,
    mul_right_comm, mul_inv_cancel₀ hnonzero, one_mul]

end Langlands.RankinSelberg
