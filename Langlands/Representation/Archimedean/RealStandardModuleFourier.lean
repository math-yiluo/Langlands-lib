import Langlands.Representation.Archimedean.StandardModule
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Fourier conditions of real standard modules under right translation and right derivatives

The block Fourier coefficients `blockFourierCoefficient N p k f g` integrate `f` against left
rotations `blockRotation N p θ`. They therefore commute with right translation, and, by
differentiation under the integral sign, with right derivatives. Consequently right translation
and right derivatives preserve the Fourier conditions defining `realStandardModule N ds` inside
the principal series.
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

/-- The exponential `exp X` of a real matrix, as an element of `GL_N(ℝ)` with inverse
`exp(-X)`. -/
def matrixExpUnit (N : ℕ) (X : Matrix (Fin N) (Fin N) ℝ) : Langlands.GeneralLinear N ℝ where
  val := NormedSpace.exp X
  inv := NormedSpace.exp (-X)
  val_inv := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl _).neg_right, add_neg_cancel,
      NormedSpace.exp_zero]
  inv_val := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl _).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]

@[simp]
theorem matrixExpUnit_val (N : ℕ) (X : Matrix (Fin N) (Fin N) ℝ) :
    (matrixExpUnit N X : Matrix (Fin N) (Fin N) ℝ) = NormedSpace.exp X :=
  rfl

theorem matrixExpUnit_zero (N : ℕ) : matrixExpUnit N 0 = 1 := by
  ext1
  simp

theorem matrixExpUnit_add_smul (N : ℕ) (X : Matrix (Fin N) (Fin N) ℝ) (s t : ℝ) :
    matrixExpUnit N ((s + t) • X) = matrixExpUnit N (s • X) * matrixExpUnit N (t • X) := by
  ext1
  simp only [matrixExpUnit_val, Units.val_mul, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)

theorem contDiff_exp_smul (N : ℕ) (X : Matrix (Fin N) (Fin N) ℝ) :
    ContDiff ℝ ∞ fun s : ℝ => NormedSpace.exp (s • X) := by
  have h : AnalyticOnNhd ℝ (NormedSpace.exp : Matrix (Fin N) (Fin N) ℝ → _) Set.univ :=
    fun x _ => NormedSpace.analyticAt_exp_of_mem_ball (𝕂 := ℝ) x
      (by rw [NormedSpace.expSeries_radius_eq_top, Metric.mem_eball]; exact edist_lt_top _ _)
  exact h.contDiff.comp (contDiff_id.smul contDiff_const)

theorem contMDiff_matrixExpUnit_smul (N : ℕ) (X : Matrix (Fin N) (Fin N) ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) (matrixModel ℝ N) ∞ fun s : ℝ => matrixExpUnit N (s • X) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  rw [contMDiff_iff_contDiff]
  exact contDiff_exp_smul N X

theorem contMDiff_blockRotation (N p : ℕ) :
    ContMDiff 𝓘(ℝ, ℝ) (matrixModel ℝ N) ∞ (blockRotation N p) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  rw [contMDiff_iff_contDiff]
  exact contDiff_exp_smul N (rotationGenerator N p)

theorem hasMFDerivAt_matrixExpUnit_smul (N : ℕ) (X : Matrix (Fin N) (Fin N) ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) (matrixModel ℝ N) (fun s : ℝ => matrixExpUnit N (s • X)) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight X) := by
  refine ⟨(contMDiff_matrixExpUnit_smul N X).continuous.continuousAt, ?_⟩
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)).hasFDerivAt
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  simp only [writtenInExtChartAt, extChartAt, mfld_simps]
  convert h.hasFDerivWithinAt using 1
  · rfl
  · ext
    rfl

theorem hasDerivAt_mul_matrixExpUnit_smul {N : ℕ} {f : Langlands.GeneralLinear N ℝ → ℂ}
    (hf : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) 1 f) (h : Langlands.GeneralLinear N ℝ)
    (X : Matrix (Fin N) (Fin N) ℝ) :
    HasDerivAt (fun s : ℝ => f (h * matrixExpUnit N (s • X)))
      (rightDerivative (matrixModel ℝ N) X f h) 0 := by
  have hF : MDifferentiableAt (matrixModel ℝ N) 𝓘(ℝ, ℂ) (fun u => f (h * u)) 1 :=
    (hf.comp (contMDiff_const.mul contMDiff_id)).mdifferentiableAt one_ne_zero
  have h0 : matrixExpUnit N ((0 : ℝ) • X) = 1 := by rw [zero_smul, matrixExpUnit_zero]
  have hF' : HasMFDerivAt (matrixModel ℝ N) 𝓘(ℝ, ℂ) (fun u => f (h * u))
      (matrixExpUnit N ((0 : ℝ) • X)) (mfderiv (matrixModel ℝ N) 𝓘(ℝ, ℂ) (fun u => f (h * u)) 1) := by
    rw [h0]
    exact hF.hasMFDerivAt
  have hcomp := HasMFDerivAt.comp (f := fun s : ℝ => matrixExpUnit N (s • X)) 0 hF'
    (hasMFDerivAt_matrixExpUnit_smul N X)
  rw [hasMFDerivAt_iff_hasFDerivAt] at hcomp
  have := hcomp.hasDerivAt
  have hv : ((mfderiv (matrixModel ℝ N) 𝓘(ℝ, ℂ) (fun u => f (h * u)) 1).comp
      ((1 : ℝ →L[ℝ] ℝ).smulRight X)) 1 =
      mfderiv (matrixModel ℝ N) 𝓘(ℝ, ℂ) (fun u => f (h * u)) 1 X := by
    simp
  exact this.congr_deriv hv

/-! ### Differentiating Fourier coefficients along right translation -/

/-- Differentiation under the integral sign for a `C¹` function of two real variables: if
`Φ : ℝ × ℝ → ℂ` is `C¹` and `Φ' θ` is the derivative of `s ↦ Φ (s, θ)` at `s₀` for every `θ`,
then `s ↦ ∫ θ in a..b, Φ (s, θ)` has derivative `∫ θ in a..b, Φ' θ` at `s₀`. -/
theorem hasDerivAt_intervalIntegral_of_contDiff {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ 1 Φ)
    {Φ' : ℝ → ℂ} {s₀ : ℝ} (hΦ' : ∀ θ, HasDerivAt (fun s => Φ (s, θ)) (Φ' θ) s₀) (a b : ℝ) :
    HasDerivAt (fun s => ∫ θ in a..b, Φ (s, θ)) (∫ θ in a..b, Φ' θ) s₀ := by
  have hpart : ∀ s θ, HasDerivAt (fun s => Φ (s, θ)) (fderiv ℝ Φ (s, θ) (1, 0)) s := fun s θ =>
    (hΦ.differentiable one_ne_zero (s, θ)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s θ))
  have hF'c : Continuous fun q : ℝ × ℝ => fderiv ℝ Φ q (1, 0) :=
    (hΦ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall s₀ 1).prod (isCompact_uIcc (a := a) (b := b))).exists_bound_of_continuousOn
      hF'c.continuousOn
  have hcont : ∀ s, Continuous fun θ => Φ (s, θ) := fun s =>
    hΦ.continuous.comp (continuous_const.prodMk continuous_id)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume) (a := a) (b := b)
    (F := fun s θ => Φ (s, θ)) (F' := fun s θ => fderiv ℝ Φ (s, θ) (1, 0)) (x₀ := s₀)
    (bound := fun _ => C) (Metric.closedBall_mem_nhds s₀ one_pos)
    (Filter.Eventually.of_forall fun s => (hcont s).aestronglyMeasurable)
    ((hcont s₀).intervalIntegrable a b)
    ((hF'c.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun θ hθ s hs =>
      hC (s, θ) (Set.mk_mem_prod hs (Set.uIoc_subset_uIcc hθ)))
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ s _ => hpart s θ)
  have heq : (fun θ => fderiv ℝ Φ (s₀, θ) (1, 0)) = Φ' := funext fun θ =>
    (hpart s₀ θ).unique (hΦ' θ)
  rw [heq] at key
  exact key.2

/-- The map `(s, θ) ↦ r_p(θ) g exp(s X)` from `ℝ × ℝ` to `GL_N(ℝ)` is smooth. -/
theorem contMDiff_blockRotation_mul_mul_matrixExpUnit (N p : ℕ) (g : Langlands.GeneralLinear N ℝ)
    (X : Matrix (Fin N) (Fin N) ℝ) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) (matrixModel ℝ N) ∞
      fun q : ℝ × ℝ => blockRotation N p q.2 * g * matrixExpUnit N (q.1 • X) := by
  have h1 : ContMDiff 𝓘(ℝ, ℝ × ℝ) (matrixModel ℝ N) ∞
      fun q : ℝ × ℝ => blockRotation N p q.2 := by
    apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
    rw [contMDiff_iff_contDiff]
    exact (contDiff_exp_smul N (rotationGenerator N p)).comp contDiff_snd
  have h2 : ContMDiff 𝓘(ℝ, ℝ × ℝ) (matrixModel ℝ N) ∞
      fun q : ℝ × ℝ => matrixExpUnit N (q.1 • X) := by
    apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
    rw [contMDiff_iff_contDiff]
    exact (contDiff_exp_smul N X).comp contDiff_fst
  exact (h1.mul contMDiff_const).mul h2

/-- For smooth `f`, the integrand `(s, θ) ↦ f(r_p(θ) g exp(s X)) e^{-ikθ}` of the block Fourier
coefficient of the right translate of `f` by `exp(s X)` is a smooth function on `ℝ × ℝ`. -/
theorem contDiff_blockFourierIntegrand {N : ℕ} {f : Langlands.GeneralLinear N ℝ → ℂ}
    (hf : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ f) (p : ℕ) (k : ℤ)
    (g : Langlands.GeneralLinear N ℝ) (X : Matrix (Fin N) (Fin N) ℝ) :
    ContDiff ℝ ∞ fun q : ℝ × ℝ =>
      f (blockRotation N p q.2 * g * matrixExpUnit N (q.1 • X)) *
        Complex.exp (-((k : ℂ) * (q.2 : ℂ) * Complex.I)) := by
  have h := hf.comp (contMDiff_blockRotation_mul_mul_matrixExpUnit N p g X)
  rw [contMDiff_iff_contDiff] at h
  have hθ : ContDiff ℝ ∞ fun q : ℝ × ℝ => (q.2 : ℂ) :=
    Complex.ofRealCLM.contDiff.comp contDiff_snd
  exact h.mul (Complex.contDiff_exp.comp ((contDiff_const.mul hθ).mul contDiff_const).neg)

/-- The block Fourier coefficients of a right translate: the coefficient of
`R(s) f = f(· s)` at `g` is the coefficient of `f` at `g s`. -/
theorem blockFourierCoefficient_rightTranslation (N p : ℕ) (k : ℤ)
    (f : Langlands.GeneralLinear N ℝ → ℂ) (s g : Langlands.GeneralLinear N ℝ) :
    blockFourierCoefficient N p k
        (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ) s f) g =
      blockFourierCoefficient N p k f (g * s) := by
  unfold blockFourierCoefficient
  refine intervalIntegral.integral_congr fun θ _ => ?_
  show f (blockRotation N p θ * g * s) * _ = f (blockRotation N p θ * (g * s)) * _
  rw [mul_assoc]

/-- If all block Fourier coefficients of index `(p, k)` of a smooth function `f` vanish, then
so do those of its right derivative along any `X`. -/
theorem blockFourierCoefficient_rightDerivative_eq_zero {N : ℕ}
    {f : Langlands.GeneralLinear N ℝ → ℂ} (hf : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ f)
    (p : ℕ) (k : ℤ) (h0 : ∀ g, blockFourierCoefficient N p k f g = 0)
    (X : Matrix (Fin N) (Fin N) ℝ) (g : Langlands.GeneralLinear N ℝ) :
    blockFourierCoefficient N p k (rightDerivative (matrixModel ℝ N) X f) g = 0 := by
  have hd := hasDerivAt_intervalIntegral_of_contDiff
    ((contDiff_blockFourierIntegrand hf p k g X).of_le (mod_cast le_top)) (s₀ := 0)
    (Φ' := fun θ => rightDerivative (matrixModel ℝ N) X f (blockRotation N p θ * g) *
      Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)))
    (fun θ => (hasDerivAt_mul_matrixExpUnit_smul (hf.of_le (mod_cast le_top)) (blockRotation N p θ * g) X).mul_const
      (Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)))) 0 (2 * Real.pi)
  have hd0 : HasDerivAt (fun _ : ℝ => (0 : ℂ))
      (∫ θ in (0 : ℝ)..2 * Real.pi, rightDerivative (matrixModel ℝ N) X f
        (blockRotation N p θ * g) * Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I))) 0 := by
    refine hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    rw [← h0 (g * matrixExpUnit N (s • X))]
    unfold blockFourierCoefficient
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [mul_assoc]
  exact hd0.unique (hasDerivAt_const 0 0)

/-! ### The Fourier conditions of `realStandardModule` -/

theorem realStandardModule_le_principalSeries (N : ℕ) (ds : List RealBlock) :
    realStandardModule N ds ≤ principalSeries ℝ N (realPositionCharacter ds) :=
  fun _ hf => hf.1

/-- Right translation preserves the Fourier conditions of `realStandardModule`: if `f` lies in
`realStandardModule N ds` and its right translate by `s` lies in the underlying principal
series, then the right translate lies in `realStandardModule N ds`. -/
theorem rightTranslation_mem_realStandardModule {N : ℕ} {ds : List RealBlock}
    {f : Langlands.GeneralLinear N ℝ → ℂ} (hf : f ∈ realStandardModule N ds)
    (s : Langlands.GeneralLinear N ℝ)
    (hs : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ) s f ∈
      principalSeries ℝ N (realPositionCharacter ds)) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ) s f ∈ realStandardModule N ds :=
  ⟨hs, fun p d hd k hk g => by
    rw [blockFourierCoefficient_rightTranslation]
    exact hf.2 p d hd k hk (g * s)⟩

/-- Right derivatives preserve the Fourier conditions of `realStandardModule`: if `f` lies in
`realStandardModule N ds` and its right derivative along `X` lies in the underlying principal
series, then the right derivative lies in `realStandardModule N ds`. -/
theorem rightDerivative_mem_realStandardModule {N : ℕ} {ds : List RealBlock}
    {f : Langlands.GeneralLinear N ℝ → ℂ} (hf : f ∈ realStandardModule N ds)
    (X : Matrix (Fin N) (Fin N) ℝ)
    (hX : rightDerivative (matrixModel ℝ N) X f ∈
      principalSeries ℝ N (realPositionCharacter ds)) :
    rightDerivative (matrixModel ℝ N) X f ∈ realStandardModule N ds :=
  ⟨hX, fun p d hd k hk g =>
    blockFourierCoefficient_rightDerivative_eq_zero hf.1.1 p k (hf.2 p d hd k hk) X g⟩

end Langlands.Archimedean
