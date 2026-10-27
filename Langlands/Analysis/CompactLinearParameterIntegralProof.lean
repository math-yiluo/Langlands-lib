import Langlands.Analysis.CompactLinearParameterIntegralStatement
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! # Proof of compact integration smoothness for continuously varying linear maps -/

noncomputable section
universe uY uV uW
open MeasureTheory Set Metric
open scoped ContDiff

namespace Langlands.Analysis

namespace CompactLinearParameterIntegral

variable {Y : Type*} [TopologicalSpace Y] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {k : Set Y} {s : Set V} {f : Y → ℂ}

/-- The partial derivative `f y • (fderiv ℝ ψ (A y x + c y)).comp (A y)` of the affine
integrand is jointly continuous on `k ×ˢ s`. -/
theorem continuousOn_partialDeriv {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {t : Set W} (ht : IsOpen t) (hf : Continuous f) {A : Y → V →L[ℝ] W} (hA : Continuous A)
    {c : Y → W} (hc : Continuous c) {ψ : W → ℂ} (hψ : ContDiffOn ℝ ∞ ψ t)
    (hAt : ∀ y ∈ k, ∀ x ∈ s, A y x + c y ∈ t) :
    ContinuousOn
      (fun p : Y × V => (f p.1) • ((fderiv ℝ ψ (A p.1 p.2 + c p.1)).comp (A p.1))) (k ×ˢ s) := by
  have hg : Continuous fun p : Y × V => A p.1 p.2 + c p.1 :=
    ((hA.comp continuous_fst).clm_apply continuous_snd).add (hc.comp continuous_fst)
  have hψd : ContinuousOn (fderiv ℝ ψ) t :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen ht).1 hψ).2.continuousOn
  exact (hf.comp continuous_fst).continuousOn.smul
    ((hψd.comp hg.continuousOn fun p hp => hAt p.1 hp.1 p.2 hp.2).clm_comp
      (hA.comp continuous_fst).continuousOn)

/-- For `x ∈ s`, the integrand `y ↦ f y * ψ (A y x + c y)` is continuous on `k`. -/
theorem continuousOn_integrand {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {t : Set W} (hf : Continuous f) {A : Y → V →L[ℝ] W} (hA : Continuous A)
    {c : Y → W} (hc : Continuous c) {ψ : W → ℂ} (hψ : ContDiffOn ℝ ∞ ψ t)
    (hAt : ∀ y ∈ k, ∀ x ∈ s, A y x + c y ∈ t) {x : V} (hx : x ∈ s) :
    ContinuousOn (fun y => f y * ψ (A y x + c y)) k :=
  hf.continuousOn.mul (hψ.continuousOn.comp
    ((hA.clm_apply continuous_const).add hc).continuousOn fun y hy => hAt y hy x hx)

variable [T2Space Y] [MeasurableSpace Y] [BorelSpace Y] [FiniteDimensional ℝ V]
  {μ : Measure Y} [IsFiniteMeasureOnCompacts μ]

/-- First derivative of the compact integral of the affine integrand
`f y * ψ (A y x + c y)`, by dominated differentiation with a constant bound. -/
theorem hasFDerivAt_integral {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (hk : IsCompact k) (hs : IsOpen s) {t : Set W} (ht : IsOpen t)
    (hf : Continuous f) {A : Y → V →L[ℝ] W} (hA : Continuous A)
    {c : Y → W} (hc : Continuous c) {ψ : W → ℂ} (hψ : ContDiffOn ℝ ∞ ψ t)
    (hAt : ∀ y ∈ k, ∀ x ∈ s, A y x + c y ∈ t) {x₀ : V} (hx₀ : x₀ ∈ s) :
    HasFDerivAt (fun x => ∫ y in k, f y * ψ (A y x + c y) ∂μ)
      (∫ y in k, (f y) • ((fderiv ℝ ψ (A y x₀ + c y)).comp (A y)) ∂μ) x₀ := by
  have hkm : MeasurableSet k := hk.measurableSet
  have hF' := continuousOn_partialDeriv ht hf hA hc hψ hAt
  obtain ⟨ε, ε_pos, hε⟩ := Metric.isOpen_iff.1 hs x₀ hx₀
  have hcb : closedBall x₀ (ε / 2) ⊆ s :=
    (closedBall_subset_ball (half_lt_self ε_pos)).trans hε
  obtain ⟨C, hC⟩ := (hk.prod (isCompact_closedBall x₀ (ε / 2))).exists_bound_of_continuousOn
    (hF'.mono (prod_mono subset_rfl hcb))
  have hψdiff : DifferentiableOn ℝ ψ t := ((contDiffOn_infty_iff_fderiv_of_isOpen ht).1 hψ).1
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := ball x₀ (ε / 2))
    (F' := fun x y => (f y) • ((fderiv ℝ ψ (A y x + c y)).comp (A y)))
    (bound := fun _ => C) (ball_mem_nhds x₀ (half_pos ε_pos)) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hs.mem_nhds hx₀] with x hx
    exact (continuousOn_integrand hf hA hc hψ hAt hx).aestronglyMeasurable_of_isCompact hk hkm
  · exact (continuousOn_integrand hf hA hc hψ hAt hx₀).integrableOn_compact hk
  · exact (hF'.comp (continuous_id.prodMk continuous_const).continuousOn
      fun y hy => ⟨hy, hx₀⟩).aestronglyMeasurable_of_isCompact hk hkm
  · exact ae_restrict_of_forall_mem hkm fun y hy x hx =>
      hC (y, x) ⟨hy, ball_subset_closedBall hx⟩
  · exact integrableOn_const hk.measure_lt_top.ne
  · refine ae_restrict_of_forall_mem hkm fun y hy x hx => ?_
    have hxt : A y x + c y ∈ t := hAt y hy x (hcb (ball_subset_closedBall hx))
    have h1 : HasFDerivAt ψ (fderiv ℝ ψ (A y x + c y)) (A y x + c y) :=
      (hψdiff.differentiableAt (ht.mem_nhds hxt)).hasFDerivAt
    exact (h1.comp x ((A y).hasFDerivAt.add_const (c y))).const_mul (f y)

/-- Every finite order of smoothness of the compact integral of the affine integrand, by
induction on the order through directional derivatives. The directional derivative in the
direction `v` is again such an integral, for the space `W × W`, the function
`p ↦ fderiv ℝ ψ p.1 p.2`, the maps `y ↦ inl ∘ A y` and the offsets `y ↦ (c y, A y v)`. -/
theorem contDiffOn_integral_nat (hk : IsCompact k) (hs : IsOpen s) (hf : Continuous f)
    (n : ℕ) :
    ∀ (W : Type uW) [NormedAddCommGroup W] [NormedSpace ℝ W]
      (t : Set W) (_ : IsOpen t) (A : Y → V →L[ℝ] W) (_ : Continuous A)
      (c : Y → W) (_ : Continuous c) (ψ : W → ℂ) (_ : ContDiffOn ℝ ∞ ψ t)
      (_ : ∀ y ∈ k, ∀ x ∈ s, A y x + c y ∈ t),
      ContDiffOn ℝ n (fun x => ∫ y in k, f y * ψ (A y x + c y) ∂μ) s := by
  induction n with
  | zero =>
    intro W _ _ t ht A hA c hc ψ hψ hAt
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun x hx =>
      (hasFDerivAt_integral hk hs ht hf hA hc hψ hAt hx).continuousAt.continuousWithinAt
  | succ n ih =>
    intro W _ _ t ht A hA c hc ψ hψ hAt
    have hD : ∀ x ∈ s, HasFDerivAt (fun x => ∫ y in k, f y * ψ (A y x + c y) ∂μ)
        (∫ y in k, (f y) • ((fderiv ℝ ψ (A y x + c y)).comp (A y)) ∂μ) x :=
      fun x hx => hasFDerivAt_integral hk hs ht hf hA hc hψ hAt hx
    have hF' := continuousOn_partialDeriv ht hf hA hc hψ hAt
    rw [Nat.cast_succ]
    refine contDiffOn_succ_of_fderiv_apply
      (fun x hx => (hD x hx).differentiableAt.differentiableWithinAt)
      (fun h => by simp at h) fun v => ?_
    have hΨ : ContDiffOn ℝ ∞ (fun p : W × W => fderiv ℝ ψ p.1 p.2) (t ×ˢ univ) :=
      (((contDiffOn_infty_iff_fderiv_of_isOpen ht).1 hψ).2.comp contDiff_fst.contDiffOn
        fun p hp => hp.1).clm_apply contDiff_snd.contDiffOn
    have key := ih (W × W) (t ×ˢ univ) (ht.prod isOpen_univ)
      (fun y => (ContinuousLinearMap.inl ℝ W W).comp (A y)) (continuous_const.clm_comp hA)
      (fun y => (c y, A y v)) (hc.prodMk (hA.clm_apply continuous_const))
      (fun p => fderiv ℝ ψ p.1 p.2) hΨ
      (fun y hy x hx => by simpa using hAt y hy x hx)
    refine key.congr fun x hx => ?_
    have hint : Integrable (fun y => (f y) • ((fderiv ℝ ψ (A y x + c y)).comp (A y)))
        (μ.restrict k) :=
      (hF'.comp (continuous_id.prodMk continuous_const).continuousOn
        fun y hy => ⟨hy, hx⟩).integrableOn_compact hk
    rw [fderivWithin_of_isOpen hs hx, (hD x hx).fderiv, ContinuousLinearMap.integral_apply hint]
    simp

end CompactLinearParameterIntegral

open CompactLinearParameterIntegral in
/-- Compact integration preserves smoothness of a linear-parameter family, and its first
derivative is the integral of the actual partial derivative. -/
theorem compactLinearParameterIntegral :
    CompactLinearParameterIntegralStatement.{uY, uV, uW} := by
  intro Y _ _ _ _ V _ _ _ W _ _ _ μ _ k hk s hs t ht f hf A hA φ hφ hAt
  have hAt' : ∀ y ∈ k, ∀ x ∈ s, A y x + (fun _ => (0 : W)) y ∈ t := by
    simpa using hAt
  have hD := fun x (hx : x ∈ s) =>
    hasFDerivAt_integral (μ := μ) hk hs ht hf hA continuous_const hφ hAt' hx
  simp only [add_zero] at hD
  refine ⟨contDiffOn_infty.2 fun n => ?_, hD⟩
  simpa using contDiffOn_integral_nat (μ := μ) hk hs hf n W t ht A hA (fun _ => 0)
    continuous_const φ hφ hAt'

end Langlands.Analysis
