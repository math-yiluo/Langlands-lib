import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Compactly supported spectral tests under a local displacement -/

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff Topology

set_option autoImplicit false

namespace Langlands.Global

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A spectral weight defined near zero displacement and a compact spectral support can
be multiplied by a cutoff in the displacement variable. The product is globally continuous
or smooth under the corresponding local regularity assumptions. -/
def CompactSpectralDisplacementStatement : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℂ) (a : ℝ × E → ℂ) (U : Set (ℝ × E)),
    IsOpen U → HasCompactSupport f → {0} ×ˢ tsupport f ⊆ U →
    ∃ g : ℝ × E → ℂ,
      (∀ t x, x ∉ tsupport f → g (t, x) = 0) ∧
      (∀ᶠ t in 𝓝 0, ∀ x, g (t, x) = f x * a (t, x)) ∧
      (Continuous f → ContinuousOn a U → Continuous g) ∧
      (ContDiff ℝ ∞ f → ContDiffOn ℝ ∞ a U → ContDiff ℝ ∞ g)

theorem compactSpectralDisplacement : CompactSpectralDisplacementStatement := by
  intro E _ _ f a U hU hf hzero
  obtain ⟨A, B, hA, _, h0A, hfB, hAB⟩ :=
    generalized_tube_lemma isCompact_singleton hf hU hzero
  obtain ⟨r, hr, hBall⟩ := Metric.isOpen_iff.mp hA 0 (h0A (mem_singleton (0 : ℝ)))
  let c : ContDiffBump (0 : ℝ) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  let cut (p : ℝ × E) := c p.1 • f p.2
  have hCut : tsupport cut ⊆ U := by
    refine (closure_minimal (t := closedBall 0 c.rOut ×ˢ tsupport f) ?_
      (isClosed_closedBall.prod isClosed_closure)).trans ?_
    · intro p hp
      have h₁ : p.1 ∈ Function.support c := by
        intro hc
        exact hp (by simp [cut, hc])
      have h₂ : p.2 ∈ Function.support f := by
        intro hf'
        exact hp (by simp [cut, hf'])
      exact ⟨ball_subset_closedBall (c.support_eq ▸ h₁), subset_closure h₂⟩
    · intro p hp
      refine hAB ⟨hBall ?_, hfB hp.2⟩
      exact lt_of_le_of_lt (mem_closedBall.mp hp.1) (half_lt_self hr)
  let g (p : ℝ × E) := cut p * a p
  have hzeroOutside {p : ℝ × E} (hp : p ∉ tsupport cut) :
      g =ᶠ[𝓝 p] fun _ => 0 := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with q hq
    change cut q = 0 at hq
    simp [g, hq]
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro t x hx
    simp [g, cut, image_eq_zero_of_notMem_tsupport hx]
  · filter_upwards [c.eventuallyEq_one] with t ht
    change c t = 1 at ht
    intro x
    simp [g, cut, ht]
  · intro hf' ha
    rw [continuous_iff_continuousAt]
    intro p
    by_cases hp : p ∈ tsupport cut
    · have h : Continuous cut := (c.continuous.comp continuous_fst).smul
        (hf'.comp continuous_snd)
      exact h.continuousAt.mul (ha.continuousAt (hU.mem_nhds (hCut hp)))
    · exact continuousAt_const.congr_of_eventuallyEq (hzeroOutside hp)
  · intro hf' ha
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p ∈ tsupport cut
    · have h : ContDiff ℝ ∞ cut := (c.contDiff.comp contDiff_fst).smul
        (hf'.comp contDiff_snd)
      exact h.contDiffAt.mul (ha.contDiffAt (hU.mem_nhds (hCut hp)))
    · exact contDiffAt_const.congr_of_eventuallyEq (hzeroOutside hp)

/-- Integration against a compact spectral test commutes with taking the displacement
to zero through any subfilter of the neighborhood filter. The integrand at zero is
absolutely integrable. -/
theorem compactSpectralIntegral_tendsto
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    {f : E → ℂ} {a : ℝ × E → ℂ} {U : Set (ℝ × E)}
    (hU : IsOpen U) (hf : Continuous f) (hfs : HasCompactSupport f)
    (ha : ContinuousOn a U) (hzero : {0} ×ˢ tsupport f ⊆ U) :
    Integrable (fun x => f x * a (0, x)) μ ∧
      Tendsto (fun t : ℝ => ∫ x, f x * a (t, x) ∂μ) (𝓝 0)
        (𝓝 (∫ x, f x * a (0, x) ∂μ)) := by
  obtain ⟨g, hgs, hgEq, hgc, _⟩ := compactSpectralDisplacement f a U hU hfs hzero
  have hg := hgc hf ha
  have h0 := hgEq.self_of_nhds
  have hgs' : HasCompactSupport (fun x => g (0, x)) := by
    exact hfs.of_isClosed_subset isClosed_closure <|
      closure_minimal (fun x hx => by
        by_contra h
        exact hx (hgs 0 x h)) isClosed_closure
  have hInt := (hg.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    (μ := μ) hgs'
  have hCont : Continuous (fun t : ℝ => ∫ x, g (t, x) ∂μ) := by
    apply continuousOn_univ.mp
    exact continuousOn_integral_of_compact_support hfs hg.continuousOn
      (fun t x _ hx => hgs t x hx)
  have hEq (t : ℝ) (ht : ∀ x, g (t, x) = f x * a (t, x)) :
      (∫ x, g (t, x) ∂μ) = ∫ x, f x * a (t, x) ∂μ :=
    integral_congr_ae (ae_of_all _ ht)
  refine ⟨hInt.congr (ae_of_all _ h0), ?_⟩
  rw [← hEq 0 h0]
  exact hCont.continuousAt.tendsto.congr' (hgEq.mono hEq)

end Langlands.Global
