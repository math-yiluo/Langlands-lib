import Langlands.Topology.CompactGroupClosedSubgroupCoverStatement
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.LocallyCompactRegular

universe uG

open Set Topology

namespace Langlands.Topology

/-- An increasing closed-subgroup cover of a compact Hausdorff topological
 group contains the whole group at some index. -/
theorem compactGroupClosedSubgroupCover :
    CompactGroupClosedSubgroupCoverStatement.{uG} := by
  intro G _ _ _ _ _ H hmono hclosed hcover
  have hUnion : (⋃ m, (H m : Set G)) = univ := by
    ext g
    simpa only [mem_iUnion, SetLike.mem_coe, mem_univ, iff_true] using hcover g
  obtain ⟨m, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hclosed hUnion
  have hopen : IsOpen (H m : Set G) :=
    (H m).isOpen_of_mem_nhds (mem_interior_iff_mem_nhds.mp hx)
  obtain ⟨n, hn⟩ := isCompact_univ.elim_directed_cover
    (fun n : ℕ => (H (max m n) : Set G))
    (fun n => Subgroup.isOpen_mono (hmono (le_max_left m n)) hopen)
    (by
      intro g _
      obtain ⟨n, hn⟩ := hcover g
      exact mem_iUnion.mpr ⟨n, hmono (le_max_right m n) hn⟩)
    (by
      intro i j
      refine ⟨max i j, ?_, ?_⟩
      · exact hmono (max_le_max_left m (le_max_left i j))
      · exact hmono (max_le_max_left m (le_max_right i j)))
  refine ⟨max m n, top_unique ?_⟩
  intro g _
  exact hn (mem_univ g)

end Langlands.Topology
