import Langlands.Global.RankinSelberg.ComplexRankZeroNormalization
import Mathlib.Analysis.Complex.Isometry
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # Polynomial normalizations of complex Tate integrals of standard Gaussians -/

noncomputable section

open Complex Filter MeasureTheory MvPolynomial Set
open scoped ComplexConjugate SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.LocalFactor.ComplexTate

private def gaussianMonomial (p q : ℕ) (z : ℂ) : ℂ := z ^ p * conj z ^ q * gaussian 0 z

private theorem eq_norm_mul_direction (z : ℂ) : z = (‖z‖ : ℂ) * direction z := by
  by_cases h : z = 0
  · simp [h]
  · rw [direction, ← mul_div_assoc, mul_comm (‖z‖ : ℂ) z,
      mul_div_cancel_right₀ _ (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h))]

private theorem conj_eq_norm_mul_inv_direction {z : ℂ} (hz : z ≠ 0) :
    conj z = (‖z‖ : ℂ) * (direction z)⁻¹ := by
  rw [direction, inv_div, ← mul_div_assoc, eq_div_iff hz, conj_mul']
  simp only [pow_two]

private theorem integrand_gaussianMonomial {z : ℂ} (hz : z ≠ 0) (p q : ℕ) (m : ℤ) (u : ℂ) :
    integrand (gaussianMonomial p q) m u z =
      direction z ^ (m + (p : ℤ) - (q : ℤ)) *
        ((‖z‖ : ℂ) ^ (p + q) * gaussian 0 z * (‖z‖ : ℂ) ^ (2 * u - 2)) := by
  have hθ := direction_ne_zero hz
  have h₁ : z ^ p = (‖z‖ : ℂ) ^ p * direction z ^ p := by
    rw [← mul_pow, ← eq_norm_mul_direction]
  have h₂ : conj z ^ q = (‖z‖ : ℂ) ^ q * (direction z)⁻¹ ^ q := by
    rw [← mul_pow, ← conj_eq_norm_mul_inv_direction hz]
  have hweight : direction z ^ (m + (p : ℤ) - (q : ℤ)) =
      direction z ^ m * direction z ^ p * (direction z)⁻¹ ^ q := by
    rw [sub_eq_add_neg, zpow_add₀ hθ, zpow_add₀ hθ, zpow_neg, zpow_natCast, zpow_natCast, inv_pow]
  rw [integrand, ite_eq_right hz, gaussianMonomial, h₁, h₂, pow_add, hweight]
  ring

private theorem zeta_gaussianMonomial_of_unmatched (p q : ℕ) (m : ℤ) (u : ℂ)
    (h : m + (p : ℤ) - (q : ℤ) ≠ 0) :
    zeta (gaussianMonomial p q) m u = 0 := by
  let k := m + (p : ℤ) - (q : ℤ)
  let a : Circle := Circle.exp (Real.pi / (k : ℝ))
  have hk : (k : ℂ) ≠ 0 := by exact_mod_cast h
  have hangle : (a : ℂ) ^ k = -1 := by
    change ((Circle.exp (Real.pi / (k : ℝ)) : Circle) : ℂ) ^ k = -1
    rw [Circle.coe_exp, ← exp_int_mul, ofReal_div, ofReal_intCast, ← mul_assoc,
      mul_div_cancel₀ _ hk, exp_pi_mul_I]
  have ha : (a : ℂ) ≠ 0 := Circle.coe_ne_zero a
  let f := integrand (gaussianMonomial p q) m u
  have hchange (z : ℂ) : f (rotation a z) = (-1 : ℂ) * f z := by
    by_cases hz : z = 0
    · simp [hz, f, integrand]
    dsimp only [f]
    rw [rotation_apply, integrand_gaussianMonomial (mul_ne_zero ha hz),
      integrand_gaussianMonomial hz, direction_mul, mul_zpow, norm_mul, Circle.norm_coe, one_mul]
    have hd : direction (a : ℂ) = (a : ℂ) := by simp [direction]
    rw [hd, hangle]
    have hG : gaussian 0 ((a : ℂ) * z) = gaussian 0 z := by simp [gaussian]
    rw [hG]
    ring
  have hI := (rotation a).measurePreserving.integral_comp (rotation a).toHomeomorph.measurableEmbedding f
  simp_rw [hchange, integral_const_mul] at hI
  rw [zeta, measure, integral_smul_measure]
  change _ • (∫ z, f z) = 0
  have hzero : (∫ z, f z) = 0 := by linear_combination -(1 / 2 : ℂ) * hI
  rw [hzero, smul_zero]

private theorem gaussian_eq_gaussianMonomial (m : ℤ) (z : ℂ) :
    gaussian m z = gaussianMonomial (-m).toNat m.toNat z := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · simp [gaussian, gaussianMonomial, mul_div_assoc]
  · by_cases h : n = 0
    · simp [h, gaussian, gaussianMonomial]
    · simp [gaussian, gaussianMonomial, h, mul_div_assoc]

private theorem matching_degrees (p q : ℕ) (m : ℤ) (h : m + (p : ℤ) - (q : ℤ) = 0) :
    p + q = m.natAbs + 2 * min p q := by
  rcases le_total p q with hpq | hqp
  · have hm : m = (q - p : ℕ) := by omega
    rw [hm, Int.natAbs_natCast, min_eq_left hpq]
    omega
  · have hm : m = -((p - q : ℕ) : ℤ) := by omega
    rw [hm, Int.natAbs_neg, Int.natAbs_natCast, min_eq_right hqp]
    omega

private theorem zeta_gaussianMonomial_of_matched (p q : ℕ) (m : ℤ) {u : ℂ}
    (hu : 0 < u.re) (h : m + (p : ℤ) - (q : ℤ) = 0) :
    zeta (gaussianMonomial p q) m u = Gammaℂ (u + (min p q : ℕ) + (m.natAbs : ℂ) / 2) := by
  have hp : 0 < (u + (min p q : ℕ)).re := by simp only [add_re, natCast_re]; positivity
  rw [← zeta_gaussian m hp]
  apply integral_congr_ae (.of_forall fun z => ?_)
  by_cases hz : z = 0
  · simp [hz, integrand]
  have hg : gaussian m = gaussianMonomial (-m).toNat m.toNat := funext (gaussian_eq_gaussianMonomial m)
  rw [integrand_gaussianMonomial hz, h, zpow_zero, one_mul, hg,
    integrand_gaussianMonomial hz]
  have hZero : m + ((-m).toNat : ℤ) - (m.toNat : ℤ) = 0 := by omega
  have hAbs : (-m).toNat + m.toNat = m.natAbs := by omega
  have hPower : (‖z‖ : ℂ) ^ (2 * min p q) * (‖z‖ : ℂ) ^ (2 * u - 2) =
      (‖z‖ : ℂ) ^ (2 * (u + (min p q : ℕ)) - 2) := by
    rw [← cpow_natCast, ← cpow_add _ _ (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))]
    congr 1
    push_cast
    ring
  rw [hZero, zpow_zero, one_mul, matching_degrees p q m h, hAbs, pow_add]
  calc
    _ = ((‖z‖ : ℂ) ^ m.natAbs * gaussian 0 z) *
        ((‖z‖ : ℂ) ^ (2 * min p q) * (‖z‖ : ℂ) ^ (2 * u - 2)) := by ring
    _ = _ := by rw [hPower]

private def gammaShiftPolynomial (m : ℤ) : ℕ → Polynomial ℂ
  | 0 => 1
  | j + 1 => (gammaShiftPolynomial m j * (Polynomial.X +
      Polynomial.C ((m.natAbs : ℂ) / 2 + (j : ℂ)))) * Polynomial.C (2 * (Real.pi : ℂ))⁻¹

private theorem natDegree_gammaShiftPolynomial_le (m : ℤ) (j : ℕ) :
    (gammaShiftPolynomial m j).natDegree ≤ j := by
  induction j with
  | zero => simp [gammaShiftPolynomial]
  | succ j ih =>
    apply (Polynomial.natDegree_mul_C_le _ _).trans
    apply (Polynomial.natDegree_mul_le_of_le ih _)
    simp only [Polynomial.natDegree_add_C, Polynomial.natDegree_X, le_rfl]

private theorem gammaShiftPolynomial_eval_mul_gamma (m : ℤ) (j : ℕ) {u : ℂ} (hu : 0 < u.re) :
    (gammaShiftPolynomial m j).eval u * Gammaℂ (u + (m.natAbs : ℂ) / 2) =
      Gammaℂ (u + (m.natAbs : ℂ) / 2 + (j : ℂ)) := by
  induction j with
  | zero => simp [gammaShiftPolynomial]
  | succ j ih =>
    have hpos : 0 < (u + (m.natAbs : ℂ) / 2 + (j : ℂ)).re := by
      simp only [add_re, div_ofNat_re, natCast_re]
      positivity
    have hh : u + (m.natAbs : ℂ) / 2 + (j : ℂ) ≠ 0 :=
      fun h => hpos.ne' (congrArg Complex.re h)
    simp only [gammaShiftPolynomial, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, Nat.cast_succ]
    rw [← add_assoc (u + (m.natAbs : ℂ) / 2), Gammaℂ_add_one hh, ← ih]
    ring

private def monomialNormalizer (m : ℤ) (p q : ℕ) : Polynomial ℂ :=
  if m + (p : ℤ) - (q : ℤ) = 0 then gammaShiftPolynomial m (min p q) else 0

private theorem natDegree_monomialNormalizer_le (m : ℤ) (p q : ℕ) :
    (monomialNormalizer m p q).natDegree ≤ min p q := by
  by_cases h : m + (p : ℤ) - (q : ℤ) = 0
  · simpa only [monomialNormalizer, ite_eq_left h] using
      natDegree_gammaShiftPolynomial_le m (min p q)
  · simp [monomialNormalizer, h]

private theorem zeta_gaussianMonomial (p q : ℕ) (m : ℤ) {u : ℂ} (hu : 0 < u.re) :
    zeta (gaussianMonomial p q) m u =
      (monomialNormalizer m p q).eval u * Gammaℂ (u + (m.natAbs : ℂ) / 2) := by
  by_cases h : m + (p : ℤ) - (q : ℤ) = 0
  · rw [monomialNormalizer, ite_eq_left h, gammaShiftPolynomial_eval_mul_gamma m (min p q) hu,
      zeta_gaussianMonomial_of_matched p q m hu h, add_right_comm]
  · simp [monomialNormalizer, h, zeta_gaussianMonomial_of_unmatched p q m u h]

private def gaussianCoordinates (z : ℂ) (b : Bool) : ℂ := if b then conj z else z

private theorem eval_gaussianCoordinates_temperate (p : MvPolynomial Bool ℂ) :
    (fun z => eval (gaussianCoordinates z) p).HasTemperateGrowth := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [eval_C] using (Function.HasTemperateGrowth.const (E := ℂ) c)
  | add p q hp hq => simpa only [map_add, Pi.add_def] using hp.add hq
  | mul_X p i hp =>
    have hi : (fun z => gaussianCoordinates z i).HasTemperateGrowth := by
      cases i
      · change (ContinuousLinearMap.id ℝ ℂ : ℂ → ℂ).HasTemperateGrowth
        exact (ContinuousLinearMap.id ℝ ℂ).hasTemperateGrowth
      · change (conjCLE : ℂ → ℂ).HasTemperateGrowth
        exact conjCLE.hasTemperateGrowth
    simpa only [map_mul, eval_X, Pi.mul_def] using hp.mul hi

/-- A polynomial in `z` and its conjugate times the standard radial Gaussian
with scale `2 * π` and coefficient `1 / π`. -/
def polynomialGaussian (p : MvPolynomial Bool ℂ) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun z => eval (gaussianCoordinates z) p) (gaussSchwartz 0)

theorem polynomialGaussian_apply (p : MvPolynomial Bool ℂ) (z : ℂ) :
    polynomialGaussian p z = eval (fun b : Bool => if b then conj z else z) p * gaussian 0 z := by
  rw [polynomialGaussian, SchwartzMap.smulLeftCLM_apply_apply (eval_gaussianCoordinates_temperate p),
    smul_eq_mul, gaussSchwartz_apply]
  rfl

private theorem polynomialGaussian_monomial (ν : Bool →₀ ℕ) (c : ℂ) :
    (polynomialGaussian (monomial ν c) : ℂ → ℂ) =
      fun z => c * gaussianMonomial (ν false) (ν true) z := by
  funext z
  rw [polynomialGaussian_apply, eval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
    Fintype.prod_bool]
  simp only [ite_true, Bool.false_eq_true, ite_false, gaussianMonomial]
  ring

private theorem zeta_polynomialGaussian_sum (p : MvPolynomial Bool ℂ) (m : ℤ) {u : ℂ}
    (hu : 0 < u.re) : zeta (polynomialGaussian p) m u =
      ∑ ν ∈ p.support, p.coeff ν * zeta (gaussianMonomial (ν false) (ν true)) m u := by
  classical
  let Φ (ν : Bool →₀ ℕ) := polynomialGaussian (monomial ν (p.coeff ν))
  have hsum (z : ℂ) : integrand (polynomialGaussian p) m u z =
      ∑ ν ∈ p.support, integrand (Φ ν) m u z := by
    have h := congrArg (eval (fun b : Bool => if b then conj z else z)) p.as_sum
    simp only [map_sum] at h
    by_cases hz : z = 0
    · simp [integrand, hz]
    · simp only [integrand, ite_eq_right hz, Φ, polynomialGaussian_apply, ← Finset.sum_mul]
      rw [← h]
  calc
    _ = ∑ ν ∈ p.support, zeta (Φ ν) m u := by
      simp only [zeta, hsum]
      exact integral_finsetSum p.support (fun ν _ => integrable_integrand (Φ ν) m hu)
    _ = _ := by
      simp only [Φ, polynomialGaussian_monomial, zeta_const_mul]

/-- The normalized complex Tate integral of a standard polynomial Gaussian is a
polynomial in the spectral variable of degree at most the degree of the test polynomial. -/
def ComplexTatePolynomialGaussianStatement : Prop :=
  ∀ (s : MvPolynomial Bool ℂ) (m : ℤ), ∃ p : Polynomial ℂ,
    p.natDegree ≤ s.totalDegree ∧ ∀ u, normalizedZeta (polynomialGaussian s) m u = p.eval u

theorem complexTatePolynomialGaussian : ComplexTatePolynomialGaussianStatement := by
  classical
  intro s m
  let p := ∑ ν ∈ s.support, s.coeff ν • monomialNormalizer m (ν false) (ν true)
  refine ⟨p, ?_, fun u => congrFun (show normalizedZeta (polynomialGaussian s) m = p.eval from ?_) u⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro ν hν
    have hdeg := le_totalDegree hν
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_bool] at hdeg
    exact (Polynomial.natDegree_smul_le _ _).trans
      ((natDegree_monomialNormalizer_le _ _ _).trans ((min_le_left _ _).trans
        ((Nat.le_add_left _ _).trans hdeg)))
  · have hN : AnalyticOnNhd ℂ (normalizedZeta (polynomialGaussian s) m) univ :=
      fun u _ => analyticAt_normalizedZeta _ _ u
    have hp : AnalyticOnNhd ℂ p.eval univ := fun u _ => p.differentiable.analyticAt u
    apply hN.eq_of_eventuallyEq hp (z₀ := 1)
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : 0 < (1 : ℂ).re)] with u hu
    have hpos : 0 < (u + (m.natAbs : ℂ) / 2).re := by
      simp only [add_re, natCast_re, div_ofNat_re]
      positivity
    have hΓ : Gammaℂ (u + (m.natAbs : ℂ) / 2) ≠ 0 := by
      rw [Gammaℂ_def]
      exact mul_ne_zero (mul_ne_zero two_ne_zero (cpow_ne_zero_iff.mpr
        (.inl (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)))))
        (Gamma_ne_zero_of_re_pos hpos)
    rw [normalizedZeta_eq_right _ _ hu, zeta_polynomialGaussian_sum s m hu]
    simp only [p, Polynomial.eval_finsetSum, Polynomial.smul_eq_C_mul, Polynomial.eval_mul,
      Polynomial.eval_C, zeta_gaussianMonomial _ _ _ hu, ← mul_assoc, ← Finset.sum_mul]
    rw [mul_assoc, mul_inv_cancel₀ hΓ, mul_one]

end Langlands.LocalFactor.ComplexTate
