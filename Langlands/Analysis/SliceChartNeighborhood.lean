import Langlands.Analysis.ComplexDistributionRealTests
import Langlands.Analysis.SliceTransverseVanishing
import Langlands.Analysis.SmoothChartDistribution

/-! # Vanishing on an open neighborhood from a real chart rectangle -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Metric Set TopologicalSpace
open scoped ContDiff Distributions

namespace Langlands.Analysis

universe uX uY uM

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {M : Type uM} [NormedAddCommGroup M] [NormedSpace ℝ M] {Ω : Opens M}

local notation "W" => (X × Y × ℝ)

private theorem normalCoordinateBox_closedBall (R : ℝ) :
    (normalCoordinateBox ⟨closedBall (0 : X × Y) R, isCompact_closedBall _ _⟩ R : Set W) =
      closedBall 0 R := by
  ext p
  rw [mem_normalCoordinateBox]
  change (p.1, p.2.1) ∈ closedBall (0 : X × Y) R ∧ p.2.2 ∈ closedBall 0 R ↔
    p ∈ closedBall 0 R
  simp only [mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
  tauto

/-- Vanishing on fixed-support real rectangles in the chart gives
an open neighborhood of the center where the ambient distribution vanishes. -/
theorem exists_chart_vanishing_neighborhood (e : OpenPartialHomeomorph W M)
    (he : ContDiffOn ℝ ∞ e e.source) (hs : ContDiffOn ℝ ∞ e.symm e.target) (h₀ : 0 ∈ e.source)
    (heΩ : e.target ⊆ Ω) (T : 𝓓(Ω, ℂ) →L[ℂ] ℂ)
    (hbox : ∀ (K₀ : Compacts (X × Y)) (R : ℝ), 0 < R →
      ∀ (hK : (normalCoordinateBox K₀ R : Set W) ⊆ e.source)
        (f : 𝓓_{normalCoordinateBox K₀ R}(W, ℝ)),
      T (smoothChartAmbientTest e hs (TestFunction.postcompCLM Complex.ofRealCLM
        (TestFunction.ofSupportedIn hK f))) = 0) :
    ∃ U : Set M, IsOpen U ∧ e 0 ∈ U ∧ U ⊆ e.target ∧ Distribution.IsVanishingOn T U := by
  obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.mp e.open_source 0 h₀
  let R := ε / 2
  have hR : 0 < R := half_pos hε
  let K₀ : Compacts (X × Y) := ⟨closedBall 0 R, isCompact_closedBall _ _⟩
  let K := normalCoordinateBox K₀ R
  have hKball : (K : Set W) = closedBall 0 R := normalCoordinateBox_closedBall R
  have hK : (K : Set W) ⊆ e.source := hKball ▸ (closedBall_subset_ball (half_lt_self hε)).trans hεs
  let V : Set W := ball 0 R
  have hVK : V ⊆ (K : Set W) := by rw [hKball]; exact ball_subset_closedBall
  have hV : V ⊆ e.source := hVK.trans hK
  let S := T.comp (smoothChartAmbientTest e hs)
  have hVanish : Distribution.IsVanishingOn S V := by
    apply (isVanishingOn_complexDistributionRealTests_iff S V).mp
    intro f hf
    let g : 𝓓_{K}(W, ℝ) :=
      ContDiffMapSupportedIn.of_support_subset f.contDiff ((subset_tsupport f).trans (hf.trans hVK))
    have hfg : TestFunction.ofSupportedIn hK g = f := TestFunction.ext fun _ => rfl
    rw [← hfg]
    exact hbox K₀ R hR hK g
  have htarget : (e '' V : Set M) ⊆ e.target := by
    rintro y ⟨z, hz, rfl⟩
    exact e.map_source (hV hz)
  exact ⟨e '' V, e.isOpen_image_of_subset_source isOpen_ball hV, ⟨0, mem_ball_self hR, rfl⟩,
    htarget, isVanishingOn_image_of_smoothChartAmbientTest e he hs heΩ T hV hVanish⟩

end Langlands.Analysis
