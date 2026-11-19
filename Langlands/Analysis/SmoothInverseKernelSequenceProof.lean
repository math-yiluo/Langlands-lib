import Langlands.Analysis.SmoothInverseKernelSequenceStatement
import Langlands.Analysis.SmoothNormalizedInverseKernelProof
import Mathlib.Order.Filter.CountablyGenerated

noncomputable section

universe uV uG

namespace Langlands.Analysis

open MeasureTheory Filter
open scoped Topology Manifold ContDiff

/-- Choose inverse-normalized kernels in symmetric refinements of a
countable decreasing neighborhood basis obtained from the original chart. -/
theorem smoothInverseKernelSequence :
    SmoothInverseKernelSequenceStatement.{uV, uG} := by
  intro V _ _ _ G _ _ _ _ _ _ _ _ μ _ _
  have : IsCountablyGenerated (𝓝 (1 : G)) := by
    rw [← (chartAt V (1 : G)).symm_map_nhds_eq (mem_chart_source V (1 : G))]
    infer_instance
  obtain ⟨B, hB⟩ := (𝓝 (1 : G)).exists_antitone_basis
  have hW (n : ℕ) : B n ∩ Inv.inv ⁻¹' B n ∈ 𝓝 (1 : G) := by
    refine inter_mem (hB.mem n) ?_
    have hBn : B n ∈ 𝓝 ((1 : G)⁻¹) := by simpa only [inv_one] using hB.mem n
    exact continuous_inv.continuousAt.preimage_mem_nhds hBn
  have hex := fun n : ℕ => smoothNormalizedInverseKernel V G μ _ (hW n)
  choose κ hs hc hsub hn hp hi hm using hex
  refine ⟨κ, fun n => ⟨hs n, hc n, hn n, hp n, hi n, hm n⟩, ?_⟩
  intro U hU
  obtain ⟨N, hNU⟩ := hB.mem_iff.mp hU
  filter_upwards [eventually_ge_atTop N] with n hnN
  have hBU : B n ⊆ U := (hB.antitone hnN).trans hNU
  have hsubB : tsupport (κ n) ⊆ B n := fun g hg => (hsub n hg).1
  refine ⟨hsubB.trans hBU, ?_⟩
  intro g hg
  have hg' : g⁻¹ ∈ tsupport (κ n) :=
    tsupport_comp_subset_preimage (κ n) continuous_inv hg
  have hginv := (hsub n hg').2
  exact hBU (by simpa only [Set.mem_preimage, inv_inv] using hginv)

end Langlands.Analysis
