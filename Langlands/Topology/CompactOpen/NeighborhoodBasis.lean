import Langlands.Topology.CompactOpen.NeighborhoodBasisStatement

open Topology

universe u

namespace Langlands

/-- Compact open subgroups form an identity-neighborhood basis. -/
theorem compactOpenSubgroupBasis : CompactOpenSubgroupBasis.{u} := by
  intro G _ _ _ _ U hU
  obtain ⟨C, hCc, hC⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨K, hK⟩ := NonarchimedeanGroup.is_nonarchimedean
    (U ∩ C) (Filter.inter_mem hU hC)
  exact ⟨K, hCc.of_isClosed_subset K.isClosed (fun _ hx => (hK hx).2),
    fun _ hx => (hK hx).1⟩

end Langlands
