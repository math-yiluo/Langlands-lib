import Langlands.GroupTheory.ProPTransport
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-! # Compact subgroups of pro-p groups -/

noncomputable section

universe u v

namespace Langlands.Cohomology

section Refinement

variable {G : Type u} [Group G] [TopologicalSpace G]
  {Q : Type v} [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [CompactSpace Q] [TotallyDisconnectedSpace Q]

/-- Every open normal subgroup in an induced group topology contains the
inverse image of an open normal subgroup of the profinite ambient group. -/
theorem exists_openNormalRefinement (f : G →* Q) (hf : Topology.IsInducing f)
    (N : OpenNormalSubgroup G) :
    ∃ M : OpenNormalSubgroup Q, M.toSubgroup.comap f ≤ N.toSubgroup := by
  obtain ⟨V, hV, hVN⟩ := hf.isOpen_iff.mp N.isOpen
  have h1 : (1 : Q) ∈ V := by
    have h : (1 : G) ∈ f ⁻¹' V := (Set.ext_iff.mp hVN 1).mpr N.one_mem
    simpa only [Set.mem_preimage, map_one] using h
  obtain ⟨M, hM⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV h1
  refine ⟨M, ?_⟩
  intro x hx
  have hxV : f x ∈ V := hM hx
  exact (Set.ext_iff.mp hVN x).mp hxV

/-- Choose an actual ambient open normal subgroup whose inverse image refines
the given open normal subgroup of the induced topology. -/
def openNormalRefinement (f : G →* Q) (hf : Topology.IsInducing f)
    (N : OpenNormalSubgroup G) :
    {M : OpenNormalSubgroup Q // M.toSubgroup.comap f ≤ N.toSubgroup} :=
  ⟨(exists_openNormalRefinement f hf N).choose,
    (exists_openNormalRefinement f hf N).choose_spec⟩

end Refinement

variable {G : Type u} [Group G] [TopologicalSpace G]
  {Q : Type v} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]

/-- A compact subgroup embedded as a topological group in a pro-p subgroup is
itself pro-p for its original subspace topology. -/
theorem IsProPSubgroup.of_isEmbedding {p : ℕ}
    {H : Subgroup G} {K : Subgroup Q} (hK : IsProPSubgroup p K)
    (f : H →* K) (hf : Topology.IsEmbedding f) (hH : IsCompact (H : Set G)) :
    IsProPSubgroup p H := by
  let : CompactSpace K := hK.compactSpace
  let : TotallyDisconnectedSpace K := hK.totallyDisconnectedSpace
  refine
    { prime := hK.prime
      compactSpace := isCompact_iff_compactSpace.mp hH
      totallyDisconnectedSpace := hf.isTotallyDisconnected_range.mp
        (isTotallyDisconnected_of_totallyDisconnectedSpace _)
      isPGroup := ?_ }
  intro N z
  refine Quotient.inductionOn' z ?_
  intro x
  let M := openNormalRefinement f hf.isInducing N
  obtain ⟨n, hn⟩ := hK.isPGroup M.val (QuotientGroup.mk (f x))
  refine ⟨n, ?_⟩
  rw [← QuotientGroup.mk_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  apply M.property
  change f (x ^ p ^ n) ∈ M.val.toSubgroup
  rw [map_pow]
  exact (QuotientGroup.eq_one_iff _).mp (by
    simpa only [QuotientGroup.mk_pow] using hn)

/-- A compact subgroup contained in a pro-p subgroup is pro-p. -/
theorem IsProPSubgroup.of_compact_le {p : ℕ} {H K : Subgroup Q}
    (hK : IsProPSubgroup p K) (hHK : H ≤ K)
    (hH : IsCompact (H : Set Q)) : IsProPSubgroup p H :=
  hK.of_isEmbedding (Subgroup.inclusion hHK) (Topology.IsEmbedding.inclusion hHK) hH

/-- A closed subgroup contained in a pro-p subgroup is pro-p. -/
theorem IsProPSubgroup.of_isClosed_le {p : ℕ} {H K : Subgroup Q}
    (hK : IsProPSubgroup p K) (hHK : H ≤ K)
    (hH : IsClosed (H : Set Q)) : IsProPSubgroup p H := by
  have hKcompact : IsCompact (K : Set Q) :=
    isCompact_iff_compactSpace.mpr hK.compactSpace
  exact hK.of_compact_le hHK (hKcompact.of_isClosed_subset hH hHK)

end Langlands.Cohomology
