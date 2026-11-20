import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Holomorphy of parametric integrals in several complex variables

A Cauchy estimate for the derivative of a holomorphic function on an open subset of `ℂⁿ`, and
the holomorphy of `s ↦ ∫ F s a ∂μ` for a finite measure `μ` when every `F · a` is holomorphic
and `F` is bounded on compact sets uniformly in `a`. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.SeveralComplex

open MeasureTheory Metric Filter Topology Set

variable {n : ℕ}

/-- **Cauchy estimate in several variables.** If `f` is holomorphic on an open set containing
the closed ball of radius `r` around `s` and bounded by `C` there, then
`‖f'(s) v‖ ≤ C / r · ‖v‖`. -/
theorem norm_fderiv_apply_le {f : (Fin n → ℂ) → ℂ} {W : Set (Fin n → ℂ)} (hW : IsOpen W)
    (hf : DifferentiableOn ℂ f W) {s : Fin n → ℂ} {r C : ℝ} (hr : 0 < r)
    (hball : closedBall s r ⊆ W) (hC : ∀ t ∈ closedBall s r, ‖f t‖ ≤ C) (v : Fin n → ℂ) :
    ‖fderiv ℂ f s v‖ ≤ C / r * ‖v‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC s (mem_closedBall_self hr.le))
    simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  set R := r / ‖v‖ with hR
  have hRpos : 0 < R := div_pos hr hvpos
  let γ : ℂ → (Fin n → ℂ) := fun z => s + z • v
  have hγ : ∀ z ∈ closedBall (0 : ℂ) R, γ z ∈ closedBall s r := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm, sub_zero] at hz
    rw [mem_closedBall, dist_eq_norm]
    simp only [γ, add_sub_cancel_left, norm_smul]
    calc ‖z‖ * ‖v‖ ≤ R * ‖v‖ := by gcongr
      _ = r := by rw [hR]; field_simp
  have hγd : ∀ z, HasDerivAt γ v z := by
    intro z
    have := ((hasDerivAt_id z).smul_const v).const_add s
    simpa [γ] using this
  have hdiff : DifferentiableOn ℂ (f ∘ γ) (closedBall 0 R) := by
    intro z hz
    have hγz : γ z ∈ W := hball (hγ z hz)
    have h1 : DifferentiableAt ℂ f (γ z) := hf.differentiableAt (hW.mem_nhds hγz)
    exact (h1.comp z (hγd z).differentiableAt).differentiableWithinAt
  have hderiv : deriv (f ∘ γ) 0 = fderiv ℂ f s v := by
    have hγ0 : γ 0 = s := by simp [γ]
    have h1 : HasFDerivAt f (fderiv ℂ f s) (γ 0) := by
      rw [hγ0]
      exact (hf.differentiableAt (hW.mem_nhds (hball (mem_closedBall_self hr.le)))).hasFDerivAt
    exact (h1.comp_hasDerivAt 0 (hγd 0)).deriv
  have hest := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRpos
    (by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball 0 hRpos.ne']
      exact hdiff)
    (fun z hz => hC _ (hγ z (sphere_subset_closedBall hz)))
  rw [show (fun z => f (γ z)) = f ∘ γ from rfl, hderiv] at hest
  calc ‖fderiv ℂ f s v‖ ≤ C / R := hest
    _ = C / r * ‖v‖ := by rw [hR]; field_simp

/-- Operator-norm form of the Cauchy estimate `norm_fderiv_apply_le`. -/
theorem norm_fderiv_le {f : (Fin n → ℂ) → ℂ} {W : Set (Fin n → ℂ)} (hW : IsOpen W)
    (hf : DifferentiableOn ℂ f W) {s : Fin n → ℂ} {r C : ℝ} (hr : 0 < r)
    (hball : closedBall s r ⊆ W) (hC : ∀ t ∈ closedBall s r, ‖f t‖ ≤ C) :
    ‖fderiv ℂ f s‖ ≤ C / r := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC s (mem_closedBall_self hr.le))
  exact ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hC0 hr.le)
    (norm_fderiv_apply_le hW hf hr hball hC)

/-- The derivative of a linear form on `ℂⁿ` in terms of its values on the standard basis. -/
theorem continuousLinearMap_eq_sum (L : (Fin n → ℂ) →L[ℂ] ℂ) :
    L = ∑ j, L (fun i => if j = i then 1 else 0) • ContinuousLinearMap.proj j := by
  ext1 v
  rw [show L v = L.toLinearMap v from rfl, LinearMap.pi_apply_eq_sum_univ L.toLinearMap v]
  simp only [ContinuousLinearMap.proj_apply, smul_eq_mul, ContinuousLinearMap.coe_coe,
    FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The derivative at `s₀` of a family of holomorphic functions, as a function of the parameter,
is almost everywhere strongly measurable when the family is, near `s₀`. -/
theorem aestronglyMeasurable_fderiv {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : (Fin n → ℂ) → α → ℂ) {s₀ : Fin n → ℂ} {r : ℝ} (hr : 0 < r)
    (hmeas : ∀ s ∈ ball s₀ r, AEStronglyMeasurable (F s) μ)
    (hdiff : ∀ a, DifferentiableAt ℂ (fun s => F s a) s₀) :
    AEStronglyMeasurable (fun a => fderiv ℂ (fun s => F s a) s₀) μ := by
  let e : Fin n → (Fin n → ℂ) := fun j i => if j = i then 1 else 0
  have he : ∀ j, ‖e j‖ ≤ 1 := by
    intro j
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    by_cases h : j = i <;> simp [e, h]
  have hcomp : ∀ j, AEStronglyMeasurable (fun a => fderiv ℂ (fun s => F s a) s₀ (e j)) μ := by
    intro j
    let t : ℕ → ℂ := fun k => ((r / ((k : ℝ) + 2) : ℝ) : ℂ)
    have htpos : ∀ k : ℕ, 0 < r / ((k : ℝ) + 2) := fun k => by positivity
    have ht0 : Tendsto t atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have h1 : Tendsto (fun k : ℕ => r / ((k : ℝ) + 2)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop
            (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
        have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
        rw [Complex.ofReal_zero] at h2
        exact h2
      · simp only [mem_compl_iff, mem_singleton_iff, t, Complex.ofReal_eq_zero]
        exact (htpos k).ne'
    have hmem : ∀ k, s₀ + t k • e j ∈ ball s₀ r := by
      intro k
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hnt : ‖t k‖ = r / ((k : ℝ) + 2) := by
        simp only [t, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (htpos k)]
      rw [hnt]
      calc r / ((k : ℝ) + 2) * ‖e j‖ ≤ r / ((k : ℝ) + 2) * 1 := by
            gcongr
            exact he j
        _ < r := by
            rw [mul_one, div_lt_iff₀ (by positivity)]
            nlinarith [hr, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun k a => (t k)⁻¹ • (F (s₀ + t k • e j) a - F s₀ a)) (fun k => ?_) ?_
    · have := ((hmeas _ (hmem k)).sub (hmeas _ (mem_ball_self hr))).const_smul (t k)⁻¹
      exact this
    · refine Eventually.of_forall fun a => ?_
      have hd : HasDerivAt (fun z : ℂ => F (s₀ + z • e j) a)
          (fderiv ℂ (fun s => F s a) s₀ (e j)) 0 := by
        have hγ : HasDerivAt (fun z : ℂ => s₀ + z • e j) (e j) 0 := by
          have := ((hasDerivAt_id (0 : ℂ)).smul_const (e j)).const_add s₀
          simpa using this
        exact (hdiff a).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ (by simp)
      have := hd.tendsto_slope.comp ht0
      refine this.congr fun k => ?_
      simp [slope_def_module]
  have hrep : (fun a => fderiv ℂ (fun s => F s a) s₀) =
      fun a => ∑ j, fderiv ℂ (fun s => F s a) s₀ (e j) • ContinuousLinearMap.proj j := by
    funext a
    exact continuousLinearMap_eq_sum _
  rw [hrep]
  exact Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hcomp j).smul_const _

/-- **Holomorphy of parametric integrals.** Let `μ` be a finite measure and `W ⊆ ℂⁿ` open. If
`F · a` is holomorphic on `W` for every `a`, `F s` is almost everywhere strongly measurable for
every `s ∈ W`, and `F` is bounded on `K × α` for every compact `K ⊆ W`, then
`s ↦ ∫ F s a ∂μ` is holomorphic on `W`. -/
theorem differentiableOn_integral_of_bounded {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (F : (Fin n → ℂ) → α → ℂ) {W : Set (Fin n → ℂ)} (hW : IsOpen W)
    (hF : ∀ a, DifferentiableOn ℂ (fun s => F s a) W)
    (hmeas : ∀ s ∈ W, AEStronglyMeasurable (F s) μ)
    (hbd : ∀ K ⊆ W, IsCompact K → ∃ C, ∀ s ∈ K, ∀ a, ‖F s a‖ ≤ C) :
    DifferentiableOn ℂ (fun s => ∫ a, F s a ∂μ) W := by
  intro s₀ hs₀
  obtain ⟨r, hr, hrW⟩ : ∃ r > 0, closedBall s₀ (2 * r) ⊆ W := by
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hW s₀ hs₀
    exact ⟨ε / 4, by positivity, (closedBall_subset_ball (by linarith)).trans hεW⟩
  obtain ⟨C, hC⟩ := hbd (closedBall s₀ (2 * r)) hrW (isCompact_closedBall _ _)
  have hballW : ball s₀ r ⊆ W := (ball_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith))).trans hrW
  have hsub : ∀ s ∈ ball s₀ r, closedBall s r ⊆ closedBall s₀ (2 * r) := by
    intro s hs t ht
    rw [mem_closedBall] at ht ⊢
    rw [mem_ball] at hs
    calc dist t s₀ ≤ dist t s + dist s s₀ := dist_triangle _ _ _
      _ ≤ 2 * r := by linarith
  have hderiv_bd : ∀ a, ∀ s ∈ ball s₀ r, ‖fderiv ℂ (fun s => F s a) s‖ ≤ max C 0 / r := by
    intro a s hs
    exact norm_fderiv_le hW (hF a) hr ((hsub s hs).trans hrW)
      (fun t ht => (hC t (hsub s hs ht) a).trans (le_max_left _ _))
  have hhas : HasFDerivAt (fun s => ∫ a, F s a ∂μ)
      (∫ a, fderiv ℂ (fun s => F s a) s₀ ∂μ) s₀ := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
      (F' := fun s a => fderiv ℂ (fun s => F s a) s) (bound := fun _ => max C 0 / r)
      (ball_mem_nhds s₀ hr) ?_ ?_ ?_ ?_ (integrable_const (μ := μ) _) ?_
    · exact Eventually.mono (hW.mem_nhds hs₀) hmeas
    · exact Integrable.of_bound (hmeas s₀ hs₀) C (Eventually.of_forall fun a =>
        hC s₀ (mem_closedBall_self (by positivity)) a)
    · exact aestronglyMeasurable_fderiv F hr (fun s hs => hmeas s (hballW hs))
        (fun a => (hF a).differentiableAt (hW.mem_nhds hs₀))
    · exact Eventually.of_forall fun a s hs => hderiv_bd a s hs
    · exact Eventually.of_forall fun a s hs =>
        ((hF a).differentiableAt (hW.mem_nhds (hballW hs))).hasFDerivAt
  exact hhas.differentiableAt.differentiableWithinAt

/-- **Holomorphy of parametric integrals in several variables** (statement form of
`differentiableOn_integral_of_bounded`, parameter space in universe `0`). -/
def ParametricIntegralHolomorphyStatement : Prop :=
  ∀ (n : ℕ) (α : Type) [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F : (Fin n → ℂ) → α → ℂ) (W : Set (Fin n → ℂ)), IsOpen W →
    (∀ a, DifferentiableOn ℂ (fun s => F s a) W) →
    (∀ s ∈ W, AEStronglyMeasurable (F s) μ) →
    (∀ K ⊆ W, IsCompact K → ∃ C, ∀ s ∈ K, ∀ a, ‖F s a‖ ≤ C) →
    DifferentiableOn ℂ (fun s => ∫ a, F s a ∂μ) W

theorem parametricIntegralHolomorphy : ParametricIntegralHolomorphyStatement :=
  fun _ _ _ μ _ F _ hW hF hmeas hbd => differentiableOn_integral_of_bounded μ F hW hF hmeas hbd

end Langlands.Analysis.SeveralComplex
