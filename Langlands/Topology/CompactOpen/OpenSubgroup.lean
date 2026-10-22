import Langlands.Topology.CompactOpen.NeighborhoodBasis
import Langlands.Topology.CompactOpen.OpenSubgroupStatement

universe u

namespace Langlands

/-- The compact open subgroups are cofinal among the open subgroups. -/
theorem openSubgroupContainsCompactOpen : OpenSubgroupContainsCompactOpen.{u} := by
  intro G _ _ _ _ H
  exact compactOpenSubgroupBasis G (H : Set G) H.mem_nhds_one

end Langlands
