import Langlands.Global.RankinSelberg.ComplexLocalEqualBoxIntegrability
import Langlands.Global.RankinSelberg.ComplexLocalEqualQuotientChange
import Langlands.Representation.Archimedean.ComplexMaximalParabolicIntegration

/-! # Convergence of the local equal-rank integral from logarithmic torus bounds -/

noncomputable section

open MeasureTheory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexLocalConvergence

open ArchimedeanLocal Langlands.Archimedean Langlands.QuotientIntegration
open ComplexCharacterChange (complexEqualIntegrand_mk)
open ComplexMaximalParabolicIntegration (normSqC normSqC_det_unitary)
open Langlands.RankinSelberg (LeftUnipotentQuotient)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "I" => Fin (r + 1)
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "N" => GeneralLinear.upperUnipotent (r + 1) ℂ
local notation "K" => unitaryCompact ℂ (r + 1)
local notation "detWeight" => ArchimedeanLocal.detPower complexNormalizedAbs
local notation "row" => Langlands.RankinSelberg.lastRow

/-- The sum of the positive parts of the logarithmic coordinates. Its value at `-x`
is the sum of the negative parts of `x` with their signs reversed. -/
def positiveLogSum (x : I → ℝ) : ℝ :=
  ∑ i, max (x i) 0

private theorem positiveLogSum_nonneg (x : I → ℝ) : 0 ≤ positiveLogSum x :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

private theorem sum_eq_positive_sub_negative (x : I → ℝ) :
    (∑ i, x i) = positiveLogSum x - positiveLogSum (-x) := by
  unfold positiveLogSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  change x i = max (x i) 0 - max (-x i) 0
  rcases le_total 0 (x i) with hi | hi
  · rw [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi), sub_zero]
  · rw [max_eq_right hi, max_eq_left (neg_nonneg.mpr hi), zero_sub, neg_neg]

private theorem sum_abs_eq_positive_add_negative (x : I → ℝ) :
    (∑ i, |x i|) = positiveLogSum x + positiveLogSum (-x) := by
  unfold positiveLogSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  change |x i| = max (x i) 0 + max (-x i) 0
  rcases le_total 0 (x i) with hi | hi
  · rw [abs_of_nonneg hi, max_eq_left hi, max_eq_right (neg_nonpos.mpr hi), add_zero]
  · rw [abs_of_nonpos hi, max_eq_right hi, max_eq_left (neg_nonneg.mpr hi), zero_add]

private theorem normalizedAbs_expDiagonal_mul (x : I → ℝ) (k : K) :
    complexNormalizedAbs (Matrix.det (expDiagonal x * k.val).val) =
      Real.exp (2 * ∑ i, x i) := by
  have hk : ‖Matrix.det k.val.val‖ ^ 2 = 1 := by
    have h := normSqC_det_unitary k
    unfold normSqC at h
    exact_mod_cast h
  simp only [complexNormalizedAbs, Units.val_mul, Matrix.det_mul, expDiagonal_val,
    Matrix.det_diagonal, norm_mul, mul_pow, hk, mul_one]
  rw [← Complex.ofReal_prod, ← Real.exp_sum, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_nonneg _), ← Real.exp_nat_mul]
  norm_num

private theorem norm_detWeight_torus (x : I → ℝ) (k : K) (s : ℂ) :
    ‖detWeight (expDiagonal x * k.val) s‖ =
      Real.exp (2 * s.re * (positiveLogSum x - positiveLogSum (-x))) := by
  unfold ArchimedeanLocal.detPower
  rw [normalizedAbs_expDiagonal_mul, Real.log_exp, Complex.norm_exp, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, sum_eq_positive_sub_negative]
  congr 1
  ring

/-- A bound for the coefficient product before the determinant twist. One exponent
controls the growth in negative logarithmic directions, and the positive directions
have arbitrarily fast exponential decay. -/
def HasLogarithmicKernelBound (F : G → ℂ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ L : ℝ, 0 ≤ L →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : I → ℝ) (k : K),
      ‖F (expDiagonal x * k.val)‖ ≤
        C * Real.exp (M * positiveLogSum (-x) - L * positiveLogSum x)

private theorem continuous_equalIntegrand {W W' : G → ℂ} {Φ : (I → ℂ) → ℂ}
    (hInv : ∀ (u : N) g, W (u.val * g) * W' (u.val * g) = W g * W' g)
    (hF : Continuous fun g => W g * W' g * Φ (row g)) (s : ℂ) :
    Continuous (complexEqualIntegrand W W' Φ s) := by
  apply (leftQuotient_isOpenQuotientMap N).isQuotientMap.continuous_iff.mpr
  have hn : Continuous fun g : G => complexNormalizedAbs (Matrix.det g.val) :=
    (continuous_norm.pow 2).comp Units.continuous_val.matrix_det
  have hlog : Continuous fun g : G => Real.log (complexNormalizedAbs (Matrix.det g.val)) :=
    hn.log fun g => pow_ne_zero 2 (norm_ne_zero_iff.mpr (GeneralLinear.determinant g).ne_zero)
  have hdet : Continuous fun g : G => detWeight g s := by
    unfold ArchimedeanLocal.detPower
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hlog))
  change Continuous fun g : G => complexEqualIntegrand W W' Φ s (Quotient.mk _ g)
  simp only [complexEqualIntegrand_mk hInv]
  change Continuous ((fun g => W g * W' g * Φ (row g)) * fun g => detWeight g s)
  exact hF.mul hdet

/-- A coefficient-product bound on the positive diagonal and right unitary factor
gives convergence of the exact quotient integrand on a right half-plane. -/
theorem exists_integrable_complexEqualIntegrand_of_logarithmicKernelBound
    {W W' : G → ℂ} {Φ : (I → ℂ) → ℂ} (D : ComplexQuotientMeasureData r)
    (hInv : ∀ (u : N) g, W (u.val * g) * W' (u.val * g) = W g * W' g)
    (hF : Continuous fun g => W g * W' g * Φ (row g))
    (hbound : HasLogarithmicKernelBound (fun g => W g * W' g * Φ (row g))) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Integrable (complexEqualIntegrand W W' Φ s) D.measure := by
  obtain ⟨b, hb, hint⟩ := exists_logDecay_threshold D
  obtain ⟨M, hM, hmajor⟩ := hbound
  refine ⟨(M + b) / 2, fun s hs => ?_⟩
  obtain ⟨C, hC, hdecay⟩ := hmajor (2 * s.re + b) (by linarith)
  apply hint (continuous_equalIntegrand hInv hF s).aestronglyMeasurable hC
  intro x k
  rw [torusPoint, complexEqualIntegrand_mk hInv, norm_mul, norm_detWeight_torus]
  let P := positiveLogSum x
  let Q := positiveLogSum (-x)
  have hQ : 0 ≤ Q := positiveLogSum_nonneg _
  have hexp : M * Q - (2 * s.re + b) * P + 2 * s.re * (P - Q) ≤ -b * (P + Q) := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * s.re - M - b by linarith) hQ]
  change _ * Real.exp (2 * s.re * (P - Q)) ≤ C * Real.exp (-b * ∑ i, |x i|)
  calc
    _ ≤ (C * Real.exp (M * Q - (2 * s.re + b) * P)) * Real.exp (2 * s.re * (P - Q)) :=
      mul_le_mul_of_nonneg_right (hdecay x k) (Real.exp_nonneg _)
    _ = C * Real.exp (M * Q - (2 * s.re + b) * P + 2 * s.re * (P - Q)) := by
      rw [mul_assoc, ← Real.exp_add]
    _ ≤ _ := by
      rw [sum_abs_eq_positive_add_negative]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hC

end Langlands.Global.RankinSelbergGlobal.ComplexLocalConvergence
