import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Separation.Regular

/-! # Cutoffs of locally smooth fields on a fixed compact set -/

noncomputable section
set_option autoImplicit false

open Function Set
open scoped ContDiff Topology

namespace Langlands.Analysis

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Multiplying a locally smooth field by a smooth cutoff extends it
globally while retaining its values on the fixed compact set. -/
theorem exists_contDiff_cutoff_smul {Ω K : Set E} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) {v : E → V} (hv : ContDiffOn ℝ ∞ v Ω) :
    ∃ a : E → ℝ, ContDiff ℝ ∞ a ∧ EqOn a 1 K ∧ tsupport a ⊆ Ω ∧
      ContDiff ℝ ∞ (fun x => a x • v x) := by
  obtain ⟨U, hU, hKU, hUΩ⟩ := hK.exists_isOpen_closure_subset (hΩ.mem_nhdsSet.mpr hKΩ)
  obtain ⟨a, ha, -, haU, haK⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hU hK.isClosed hKU
  have hs : tsupport a ⊆ Ω := by rwa [tsupport, haU]
  refine ⟨a, ha, fun x hx => (haK x).mp hx, hs, contDiff_iff_contDiffAt.mpr ?_⟩
  intro x
  by_cases hx : x ∈ Ω
  · exact ha.contDiffAt.smul (hv.contDiffAt (hΩ.mem_nhds hx))
  · have hx' : x ∉ tsupport a := fun h => hx (hs h)
    apply (contDiffAt_const (c := (0 : V))).congr_of_eventuallyEq
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx'] with y hy
    rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]

end Langlands.Analysis
