import Langlands.Representation.Jacquet.CompactUnionCoinvariantStatements
import Langlands.Topology.LocallyProfiniteProof

/-! # Compact containment for a filtered union of compact subgroups -/

namespace Langlands.Jacquet

universe uH

/-- Renard III.2.9, the compact-containment remark. -/
theorem compactSubgroupFilteredUnion :
    CompactSubgroupFilteredUnionStatement.{uH} := by
  classical
  intro H _ _ _ _ _ _ hcover hfilter C hC
  obtain ⟨U, hU, -⟩ :=
    ((Langlands.Topology.LocallyProfiniteProof.vanDantzig H).mp
      Langlands.Topology.isLocallyProfinite_of_mathlib).2 Set.univ Filter.univ_mem
  have hpoint (x : H) :
      ∃ K : {K : Subgroup H // IsCompact (K : Set H)},
        x ∈ K.1 ∧ IsOpen (K.1 : Set H) := by
    have hx : x ∈ ⋃ K : {K : Subgroup H // IsCompact (K : Set H)}, (K.1 : Set H) := by
      rw [hcover]
      trivial
    obtain ⟨K, hxK⟩ := Set.mem_iUnion.mp hx
    let Uc : {K : Subgroup H // IsCompact (K : Set H)} := ⟨U.toSubgroup, hU⟩
    obtain ⟨L, hL⟩ := hfilter {K, Uc}
    have hKL : K.1 ≤ L.1 := by
      intro y hy
      apply hL
      simp only [Set.mem_iUnion]
      exact ⟨K, by simp, hy⟩
    have hUL : U.toSubgroup ≤ L.1 := by
      intro y hy
      apply hL
      simp only [Set.mem_iUnion]
      exact ⟨Uc, by simp, hy⟩
    exact ⟨L, hKL hxK, Subgroup.isOpen_mono hUL U.isOpen⟩
  choose K hK hopen using hpoint
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover (fun x => (K x).1 : H → Set H) hopen
    (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, hK x⟩)
  obtain ⟨L, hL⟩ := hfilter (s.image K)
  refine ⟨L.1, L.2, fun x hx => ?_⟩
  have hxcover := hs hx
  simp only [Set.mem_iUnion] at hxcover
  obtain ⟨y, hy, hxy⟩ := hxcover
  apply hL
  simp only [Set.mem_iUnion]
  exact ⟨K y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, hxy⟩

end Langlands.Jacquet
