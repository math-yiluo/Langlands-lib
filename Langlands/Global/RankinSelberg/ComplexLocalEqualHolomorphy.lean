import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Holomorphy of absolutely convergent complex local integrals -/

noncomputable section

open MeasureTheory
open scoped Topology

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

private theorem exp_mul_abs_le {c y δ x : ℝ} (hδ : 0 < δ)
    (hy₁ : c - δ ≤ y) (hy₂ : y ≤ c + δ) :
    Real.exp (y * x) * |x| ≤ δ⁻¹ *
      (Real.exp ((c - 2 * δ) * x) + Real.exp ((c + 2 * δ) * x)) := by
  have hx : |x| ≤ δ⁻¹ * Real.exp (δ * |x|) := by
    rw [← div_eq_inv_mul, le_div_iff₀ hδ, mul_comm |x| δ]
    linarith [Real.add_one_le_exp (δ * |x|)]
  calc
    Real.exp (y * x) * |x| ≤ Real.exp (y * x) * (δ⁻¹ * Real.exp (δ * |x|)) :=
      mul_le_mul_of_nonneg_left hx (Real.exp_nonneg _)
    _ = δ⁻¹ * Real.exp (y * x + δ * |x|) := by rw [Real.exp_add]; ring
    _ ≤ δ⁻¹ * (Real.exp ((c - 2 * δ) * x) + Real.exp ((c + 2 * δ) * x)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hδ.le)
      rcases le_or_gt 0 x with hx₀ | hx₀
      · rw [abs_of_nonneg hx₀, ← add_mul]
        exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hx₀)).trans
          (le_add_of_nonneg_left (Real.exp_nonneg _))
      · rw [abs_of_neg hx₀, mul_neg, ← sub_eq_add_neg, ← sub_mul]
        exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (by linarith) hx₀.le)).trans
          (le_add_of_nonneg_right (Real.exp_nonneg _))

/-- A complex exponential integral is holomorphic on an open set of absolute convergence.
The coefficient need only be a.e. strongly measurable after twisting. -/
theorem differentiableOn_integral_mul_cexp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A : α → ℂ} {B : α → ℝ} (hB : Measurable B) {S : Set ℂ} (hS : IsOpen S)
    (hInt : ∀ s ∈ S, Integrable (fun q => A q * Complex.exp (s * (B q : ℂ))) μ) :
    DifferentiableOn ℂ (fun s => ∫ q, A q * Complex.exp (s * (B q : ℂ)) ∂μ) S := by
  let F (s : ℂ) (q : α) := A q * Complex.exp (s * (B q : ℂ))
  let F' (s : ℂ) (q : α) := F s q * (B q : ℂ)
  intro s₀ hs₀
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hS s₀ hs₀
  let δ := R / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let low : ℂ := s₀ - (2 * δ : ℝ)
  let high : ℂ := s₀ + (2 * δ : ℝ)
  have hshift : ‖((2 * δ : ℝ) : ℂ)‖ < R := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * δ)]
    dsimp [δ]
    linarith
  have hl : low ∈ S := hball (by
    change dist (s₀ - (2 * δ : ℝ)) s₀ < R
    rwa [dist_eq_norm, sub_right_comm, sub_self, zero_sub, norm_neg])
  have hh : high ∈ S := hball (by
    change dist (s₀ + (2 * δ : ℝ)) s₀ < R
    rwa [dist_eq_norm, add_sub_cancel_left])
  let bound (q : α) := δ⁻¹ * (‖F low q‖ + ‖F high q‖)
  have hbound : Integrable bound μ :=
    ((hInt low hl).norm.add (hInt high hh).norm).const_mul _
  have hnear : ∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable (F s) μ :=
    Filter.Eventually.mono (hS.mem_nhds hs₀) fun s hs => (hInt s hs).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (F' s₀) μ :=
    (hInt s₀ hs₀).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.measurable.comp hB).aestronglyMeasurable
  have hderiv (s : ℂ) (q : α) : HasDerivAt (fun z => F z q) (F' s q) s := by
    simpa [F, F', mul_assoc] using
      (((hasDerivAt_id s).mul_const (B q : ℂ)).cexp.const_mul (A q))
  have hnorm (s : ℂ) (q : α) : ‖F s q‖ = ‖A q‖ * Real.exp (s.re * B q) := by
    simp [F, Complex.norm_exp, Complex.mul_re]
  let U : Set ℂ := {s | s₀.re - δ < s.re ∧ s.re < s₀.re + δ}
  have hopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hU : U ∈ 𝓝 s₀ := hopen.mem_nhds
    (show s₀.re - δ < s₀.re ∧ s₀.re < s₀.re + δ from ⟨by linarith, by linarith⟩)
  have hdom (q : α) (s : ℂ) (hs : s ∈ U) : ‖F' s q‖ ≤ bound q := by
    change s₀.re - δ < s.re ∧ s.re < s₀.re + δ at hs
    have h := mul_le_mul_of_nonneg_left (exp_mul_abs_le hδ hs.1.le hs.2.le (x := B q))
      (norm_nonneg (A q))
    rw [show ‖F' s q‖ = ‖A q‖ * (Real.exp (s.re * B q) * |B q|) by
      rw [show F' s q = F s q * (B q : ℂ) by rfl, norm_mul, hnorm, Complex.norm_real,
        Real.norm_eq_abs, mul_assoc]]
    dsimp [bound]
    rw [hnorm, hnorm, ← mul_add, mul_comm δ⁻¹, mul_assoc]
    simpa [low, high, mul_comm δ⁻¹] using h
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hU hnear (hInt s₀ hs₀) hmeas'
    (Filter.Eventually.of_forall hdom) hbound
    (Filter.Eventually.of_forall fun q s _ => hderiv s q)).2.differentiableAt.differentiableWithinAt

open ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient lastRow)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

/-- The real logarithm of the squared determinant norm, descended to the unipotent quotient. -/
def complexQuotientLogDet {r : ℕ} : LeftUnipotentQuotient r ℂ → ℝ :=
  QuotientIntegration.descend (GeneralLinear.upperUnipotent (r + 1) ℂ)
    (fun g => Real.log (complexNormalizedAbs (Matrix.det g.val))) (by
      intro u g
      simp only [Units.val_mul, Matrix.det_mul, RankinSelberg.unipotent_det, one_mul])

theorem complexQuotientLogDet_out {r : ℕ} (q : LeftUnipotentQuotient r ℂ) :
    complexQuotientLogDet q = Real.log (complexNormalizedAbs (Matrix.det q.out.val)) := by
  conv_lhs => rw [← Quotient.out_eq q]
  rfl

theorem continuous_complexQuotientLogDet {r : ℕ} :
    Continuous (@complexQuotientLogDet r) := by
  unfold complexQuotientLogDet QuotientIntegration.descend
  apply Continuous.quotient_lift
  have hnorm : Continuous (fun g : Langlands.GeneralLinear (r + 1) ℂ =>
      complexNormalizedAbs (Matrix.det g.val)) :=
    (continuous_norm.pow 2).comp (Units.continuous_val.comp
      Matrix.GeneralLinearGroup.continuous_det)
  refine continuous_iff_continuousAt.mpr fun g => ?_
  have hg : complexNormalizedAbs (Matrix.det g.val) ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr (GeneralLinear.determinant g).ne_zero)
  have hlog : ContinuousAt Real.log
      ((fun g : Langlands.GeneralLinear (r + 1) ℂ =>
        complexNormalizedAbs (Matrix.det g.val)) g) :=
    Real.continuousAt_log hg
  exact hlog.comp (x := g) hnorm.continuousAt

/-- Absolute convergence of the exact complex equal-rank integrand on an open set implies
holomorphy of its integral there. -/
theorem differentiableOn_complexEqualIntegral {r : ℕ} (D : ComplexQuotientMeasureData r)
    (W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (Φ : (Fin (r + 1) → ℂ) → ℂ)
    {S : Set ℂ} (hS : IsOpen S)
    (hInt : ∀ s ∈ S, Integrable (complexEqualIntegrand W W' Φ s) D.measure) :
    DifferentiableOn ℂ (complexEqualIntegral D W W' Φ) S := by
  let A (q : LeftUnipotentQuotient r ℂ) := W q.out * W' q.out * Φ (lastRow q.out)
  have hEq (s : ℂ) (q : LeftUnipotentQuotient r ℂ) :
      complexEqualIntegrand W W' Φ s q = A q * Complex.exp (s * (complexQuotientLogDet q : ℂ)) := by
    rw [complexQuotientLogDet_out]
    rfl
  have hFun : complexEqualIntegral D W W' Φ =
      fun s => ∫ q, A q * Complex.exp (s * (complexQuotientLogDet q : ℂ)) ∂D.measure := by
    funext s
    change (∫ q, complexEqualIntegrand W W' Φ s q ∂D.measure) = _
    exact integral_congr_ae (Filter.Eventually.of_forall (hEq s))
  rw [hFun]
  apply differentiableOn_integral_mul_cexp continuous_complexQuotientLogDet.measurable hS
  exact fun s hs => (hInt s hs).congr (Filter.Eventually.of_forall (hEq s))

end Langlands.Global.RankinSelbergGlobal
