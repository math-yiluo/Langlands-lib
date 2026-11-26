import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! # Polynomial Fourier tests and transposed directional derivatives -/

noncomputable section

open MeasureTheory
open scoped FourierTransform LineDeriv SchwartzMap

set_option autoImplicit false

namespace Langlands.Analysis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

private def derivativeScalar : ℂ := -(2 * (Real.pi : ℂ) * Complex.I)

private theorem derivativeScalar_ne_zero : derivativeScalar ≠ 0 := by
  unfold derivativeScalar
  exact neg_ne_zero.mpr
    (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero)

private theorem fourierInv_iteratedDerivative_apply {n : ℕ} (m : Fin n → V)
    (a : 𝓢(V, ℂ)) (x : V) :
    (𝓕⁻ (∂^{m} a)) x =
      derivativeScalar ^ n * (∏ i, ((inner ℝ x (m i) : ℝ) : ℂ)) * (𝓕⁻ a) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : (fun v => inner ℝ v (m 0)).HasTemperateGrowth := by fun_prop
    rw [LineDeriv.iteratedLineDerivOp_succ_left, SchwartzMap.fourierInv_lineDerivOp_eq,
      smul_apply, SchwartzMap.smulLeftCLM_apply_apply h, ih,
      Fin.prod_univ_succ, pow_succ]
    simp only [derivativeScalar, Complex.real_smul, smul_eq_mul, Fin.tail_def]
    ring

/-- Testing a monomial times a unitary character against a positive Fourier transform gives
a derivative of the test evaluated at the character's parameter. Each derivative on the
test has the negative scalar dictated by transposition. -/
def SchwartzPolynomialFourierTestStatement : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {n : ℕ} (m : Fin n → V) (a : 𝓢(V, ℂ)) (ξ : V),
    let g (x : V) := Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) *
      (∏ i, ((inner ℝ x (m i) : ℝ) : ℂ)) * (𝓕⁻ a) x
    Integrable g ∧ (∫ x, g x) =
      (-(2 * (Real.pi : ℂ) * Complex.I))⁻¹ ^ n * (∂^{m} a) ξ

theorem schwartzPolynomialFourierTest : SchwartzPolynomialFourierTestStatement := by
  intro V _ _ _ _ _ n m a ξ
  dsimp only
  let b : 𝓢(V, ℂ) := 𝓕⁻ (∂^{m} a)
  let phase (x : V) := Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I)
  have hnorm (x : V) : ‖phase x‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hphase : Continuous phase := by
    unfold phase
    fun_prop
  have hI : Integrable (fun x => phase x * b x) :=
    b.integrable.mono (hphase.mul b.continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [norm_mul, hnorm, one_mul])
  have hfactor (x : V) :
      phase x * (∏ i, ((inner ℝ x (m i) : ℝ) : ℂ)) * (𝓕⁻ a) x =
        derivativeScalar⁻¹ ^ n * (phase x * b x) := by
    unfold b
    rw [fourierInv_iteratedDerivative_apply]
    have hcancel : derivativeScalar⁻¹ ^ n * derivativeScalar ^ n = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ derivativeScalar_ne_zero, one_pow]
    calc
      _ = (derivativeScalar⁻¹ ^ n * derivativeScalar ^ n) *
          (phase x * (∏ i, ((inner ℝ x (m i) : ℝ) : ℂ)) * (𝓕⁻ a) x) := by
        rw [hcancel, one_mul]
      _ = _ := by ring
  change Integrable (fun x => phase x * (∏ i, ((inner ℝ x (m i) : ℝ) : ℂ)) * (𝓕⁻ a) x) ∧
    (∫ x, phase x * (∏ i, ((inner ℝ x (m i) : ℝ) : ℂ)) * (𝓕⁻ a) x) = _
  simp_rw [hfactor]
  refine ⟨hI.const_mul _, ?_⟩
  have hFourier : (∫ x, phase x * b x) = (𝓕 b) ξ := by
    simp only [SchwartzMap.fourier_coe, Real.fourier_eq', phase, smul_eq_mul]
  rw [integral_const_mul, hFourier]
  simp [b, derivativeScalar]

end Langlands.Analysis
