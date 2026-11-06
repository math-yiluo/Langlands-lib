import Langlands.Shimura.Levels
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-! # Compact open refinements normal in a prescribed compact open level -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shimura.CompactOpenLevel

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- An actual compact open common refinement, normal in the coarse level. -/
structure NormalRefinement (U V : CompactOpenLevel G) where
  level : CompactOpenLevel G
  le_coarse : level.subgroup ≤ U.subgroup
  le_fine : level.subgroup ≤ V.subgroup
  normal_coarse : (level.subgroup.subgroupOf U.subgroup).Normal

/-- Choose an open normal subgroup inside the preimage of the fine level in
the compact coarse group, and map it into the original group. -/
def normalRefinement (U V : CompactOpenLevel G) : NormalRefinement U V := by
  letI : CompactSpace U.subgroup := isCompact_iff_compactSpace.mp U.isCompact
  let T : OpenSubgroup U.subgroup :=
    V.openSubgroup.comap U.subgroup.subtype continuous_subtype_val
  have hex : ∃ H : OpenNormalSubgroup U.subgroup, (H : Set U.subgroup) ⊆ T :=
    IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
      ⟨T.isClosed, T.isOpen⟩ T.one_mem
  let H := Classical.choose hex
  have hH : (H : Set U.subgroup) ⊆ T := Classical.choose_spec hex
  let W : OpenSubgroup G :=
    { toSubgroup := H.toSubgroup.map U.subgroup.subtype
      isOpen' := by
        change IsOpen (U.subgroup.subtype '' (H : Set U.subgroup))
        exact U.openSubgroup.isOpen.isOpenMap_subtype_val _ H.toOpenSubgroup.isOpen }
  have hWU : W.toSubgroup ≤ U.subgroup := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  refine
    { level := ⟨W, U.isCompact.of_isClosed_subset W.isClosed hWU⟩
      le_coarse := hWU
      le_fine := ?_
      normal_coarse := ?_ }
  · rintro x ⟨y, hy, rfl⟩
    exact hH hy
  · apply (Subgroup.normal_subgroupOf_iff hWU).mpr
    intro x u hx hu
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨⟨u, hu⟩ * y * ⟨u, hu⟩⁻¹,
      H.isNormal'.conj_mem y hy ⟨u, hu⟩, rfl⟩

namespace NormalRefinement

variable {U V : CompactOpenLevel G} (W : NormalRefinement U V)

omit [IsTopologicalGroup G] in
/-- Normality in the coarse level restricts to every intermediate fine level. -/
theorem normal_fine (hVU : V.subgroup ≤ U.subgroup) :
    (W.level.subgroup.subgroupOf V.subgroup).Normal := by
  apply (Subgroup.normal_subgroupOf_iff W.le_fine).mpr
  intro x v hx hv
  exact (Subgroup.normal_subgroupOf_iff W.le_coarse).mp W.normal_coarse
    x v hx (hVU hv)

end NormalRefinement
end Langlands.Shimura.CompactOpenLevel
