import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.UniformSpace.UniformApproximation
import Langlands.Analysis.ExponentialSectorLimit

/-! # Decay of exponentially Cauchy differences with vanishing smooth tests -/

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Topology

set_option autoImplicit false

namespace Langlands.Analysis

/-- A comparable-increment bound, locally uniform in the spectral parameter, and vanishing of
all limiting smooth compact tests force exponential decay of the difference itself. Any
increment constants that work on a specified subset give the displayed decay bound there. -/
def TestedExponentialSectorStatement : Prop :=
  ∀ {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    [μ.IsOpenPosMeasure] (C : Set V) (U : Set X) (f : V → X → ℂ) (R : ℝ),
    let l := comap (fun t : V => ‖t‖) atTop ⊓ 𝓟 C
    let Increments (A : Set X) (B ε : ℝ) :=
      ∀ x ∈ A, ∀ t ∈ C, ∀ s ∈ C, R ≤ ‖t‖ → ‖s‖ ≤ ‖t‖ →
        dist (f t x) (f (t + s) x) ≤ B * Real.exp (-ε * ‖t‖)
    1 ≤ R → (∃ u ∈ C, ‖u‖ = 1) →
    (∀ t ∈ C, ∀ r : ℝ, 0 < r → r • t ∈ C) → IsOpen U →
    (∀ᶠ t in l, ContinuousOn (f t) U) →
    (∀ A ⊆ U, IsCompact A → ∃ B ε : ℝ, 0 ≤ B ∧ 0 < ε ∧ Increments A B ε) →
    (∀ β : X → ℝ, ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ U →
      Tendsto (fun t => ∫ x, β x • f t x ∂μ) l (𝓝 0)) →
    ∀ A ⊆ U, ∀ B ε : ℝ, 0 ≤ B → 0 < ε → Increments A B ε →
      ∀ x ∈ A, ∀ t ∈ C, R ≤ ‖t‖ →
        ‖f t x‖ ≤ B * Real.exp (-ε * ‖t‖) / (1 - Real.exp (-ε))

private theorem continuous_smul_of_tsupport_subset
    {X : Type*} [NormedAddCommGroup X] {U : Set X} (hU : IsOpen U)
    {β : X → ℝ} (hβ : Continuous β) (hβU : tsupport β ⊆ U)
    {g : X → ℂ} (hg : ContinuousOn g U) : Continuous (fun x => β x • g x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ tsupport β
  · exact hβ.continuousAt.smul (hg.continuousAt (hU.mem_nhds (hβU hx)))
  · have hlocal : (fun y => β y • g y) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
      change β y = 0 at hy
      simp [hy]
    exact continuousAt_const.congr_of_eventuallyEq hlocal

theorem testedExponentialSector : TestedExponentialSectorStatement := by
  classical
  intro V X _ _ _ _ _ _ _ μ _ _ C U f R l Increments hR hunit hscale hU hf hinc htest
  have hnorm : Tendsto (fun t : V => ‖t‖) l atTop :=
    (tendsto_comap : Tendsto (fun t : V => ‖t‖) _ atTop).mono_left inf_le_left
  have hmem : ∀ᶠ t in l, t ∈ C := le_principal_iff.mp inf_le_right
  have hray : ∃ u : V, Tendsto (fun r : ℝ => r • u) atTop l := by
    obtain ⟨u, hu, hun⟩ := hunit
    refine ⟨u, tendsto_inf.2 ⟨?_, tendsto_principal.2 ?_⟩⟩
    · apply tendsto_comap_iff.2
      apply tendsto_id.congr'
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
      simp [norm_smul, Real.norm_of_nonneg hr, hun]
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      exact hscale u hu r hr
  have : l.NeBot := (hray.choose_spec : Tendsto _ atTop l).neBot
  have hlimit (x : X) (hx : x ∈ U) : ∃ z : ℂ, Tendsto (fun t => f t x) l (𝓝 z) := by
    obtain ⟨B, ε, hB, hε, hstep⟩ := hinc {x} (singleton_subset_iff.mpr hx) isCompact_singleton
    obtain ⟨z, hz, _⟩ := exponentialSectorLimit C (fun t => f t x) R B ε hR hB hε hunit hscale
      (hstep x (mem_singleton x))
    exact ⟨z, hz⟩
  let L (x : X) : ℂ := if hx : x ∈ U then (hlimit x hx).choose else 0
  have hL (x : X) (hx : x ∈ U) : Tendsto (fun t => f t x) l (𝓝 (L x)) := by
    simpa only [L, dite_eq_left hx] using (hlimit x hx).choose_spec
  have hbound (A : Set X) (hA : A ⊆ U) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε)
      (hstep : Increments A B ε) (x : X) (hx : x ∈ A) (t : V) (ht : t ∈ C) (hrt : R ≤ ‖t‖) :
      dist (f t x) (L x) ≤ B * Real.exp (-ε * ‖t‖) / (1 - Real.exp (-ε)) := by
    obtain ⟨z, hz, htail⟩ := exponentialSectorLimit C (fun t => f t x) R B ε hR hB hε hunit hscale
      (hstep x hx)
    rw [← tendsto_nhds_unique hz (hL x (hA hx))]
    exact htail t ht hrt
  have huniform : TendstoLocallyUniformlyOn f L l U := by
    refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).2 fun A hA hAc => ?_
    obtain ⟨B, ε, hB, hε, hstep⟩ := hinc A hA hAc
    have hdecay : Tendsto (fun t : V => B * Real.exp (-ε * ‖t‖) / (1 - Real.exp (-ε))) l (𝓝 0) := by
      have he := Real.tendsto_exp_atBot.comp (hnorm.const_mul_atTop_of_neg (neg_neg_of_pos hε))
      simpa only [Function.comp_apply, mul_zero, zero_div] using
        (he.const_mul B).div_const (1 - Real.exp (-ε))
    refine Metric.tendstoUniformlyOn_iff.2 fun a ha => ?_
    filter_upwards [hmem, hnorm.eventually_ge_atTop R, hdecay.eventually_lt_const ha] with t ht hrt hsmall
    intro x hx
    rw [dist_comm]
    exact (hbound A hA B ε hB hε hstep x hx t ht hrt).trans_lt hsmall
  have hLc := huniform.continuousOn hf.frequently
  have hLtest (β : X → ℝ) (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
      (hβU : tsupport β ⊆ U) : ∫ x, β x • L x ∂μ = 0 := by
    let g (x : X) : ℂ := β x • L x
    have hgi : Integrable g μ :=
      (continuous_smul_of_tsupport_subset hU hβ.continuous hβU hLc).integrable_of_hasCompactSupport
        hβc.smul_right
    have hconv : Tendsto (fun t => ∫ x, β x • f t x ∂μ) l (𝓝 (∫ x, g x ∂μ)) := by
      have hmeas : ∀ᶠ t in l, AEStronglyMeasurable (fun x => β x • f t x) μ := by
        filter_upwards [hf] with t hft
        exact (continuous_smul_of_tsupport_subset hU hβ.continuous hβU hft).aestronglyMeasurable
      have hclose := Metric.tendstoUniformlyOn_iff.1
        ((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 huniform
          (tsupport β) hβU hβc.isCompact) 1 zero_lt_one
      have hdom : ∀ᶠ t in l, ∀ᵐ x ∂μ, ‖β x • f t x‖ ≤ ‖β x‖ + ‖g x‖ := by
        filter_upwards [hclose] with t ht using ae_of_all _ fun x => by
          by_cases hx : x ∈ tsupport β
          · have hd : ‖f t x - L x‖ ≤ 1 := by
              rw [← dist_eq_norm, dist_comm]
              exact (ht x hx).le
            calc
              _ = ‖β x • (f t x - L x) + g x‖ := by
                change ‖β x • f t x‖ = ‖β x • (f t x - L x) + β x • L x‖
                rw [← smul_add, sub_add_cancel]
              _ ≤ ‖β x • (f t x - L x)‖ + ‖g x‖ := norm_add_le _ _
              _ ≤ _ := by
                rw [norm_smul]
                exact add_le_add (mul_le_of_le_one_right (norm_nonneg _) hd) le_rfl
          · simp [g, image_eq_zero_of_notMem_tsupport hx]
      have hpoint : ∀ᵐ x ∂μ, Tendsto (fun t => β x • f t x) l (𝓝 (g x)) := ae_of_all _ fun x => by
        by_cases hx : x ∈ tsupport β
        · exact (hL x (hβU hx)).const_smul (β x)
        · simp [g, image_eq_zero_of_notMem_tsupport hx]
      exact tendsto_integral_filter_of_dominated_convergence (fun x => ‖β x‖ + ‖g x‖) hmeas hdom
        ((hβ.continuous.integrable_of_hasCompactSupport hβc).norm.add hgi.norm) hpoint
    exact tendsto_nhds_unique hconv (htest β hβ hβc hβU)
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hLc.locallyIntegrableOn hU.measurableSet) hLtest
  have hzero : EqOn L (fun _ => (0 : ℂ)) U :=
    Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).2 hae) hU hLc continuousOn_const
  intro A hA B ε hB hε hstep x hx t ht hrt
  simpa only [hzero (hA hx), dist_zero_right] using hbound A hA B ε hB hε hstep x hx t ht hrt

end Langlands.Analysis
