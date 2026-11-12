import Langlands.BruhatTits.SpecialCompact.SmallSubgroupPredicates
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-! # Normal compact-open bases and their literal closed-subgroup intersections -/

universe u
open Set Filter Topology

namespace Langlands.BruhatTits.SpecialCompact

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [IsTopologicalGroup H] in
/-- Any normal compact-open identity basis restricts to the same literal
intersection family on every closed subgroup. -/
theorem CompactOpenNormalBasis.inherited {K0 M : Subgroup H} {B : Set (Subgroup H)}
    (hB : CompactOpenNormalBasis K0 B) (hM : IsClosed (M : Set H)) :
    InheritedCompactOpenNormalBasis K0 M B := by
  constructor
  · rintro L ⟨K, hK, rfl⟩
    obtain ⟨hKK0, hnormal, hopen, hcompact⟩ := hB.1 K hK
    refine ⟨Subgroup.comap_mono hKK0, ?_,
      hopen.preimage continuous_subtype_val,
      hM.isClosedEmbedding_subtypeVal.isCompact_preimage hcompact⟩
    constructor
    intro n hn g
    exact hnormal.conj_mem ⟨(n : M), hKK0 hn⟩ hn ⟨(g : M), g.property⟩
  · change (𝓝 (1 : M)).HasBasis (fun L => L ∈ intersectionFamily M B)
      (fun L => (L : Set M))
    rw [nhds_subtype_eq_comap]
    exact (hB.2.comap M.subtype).to_hasBasis
      (fun K hK => ⟨K.comap M.subtype, ⟨K, hK, rfl⟩, subset_rfl⟩)
      (fun L hL => by
        obtain ⟨K, hK, rfl⟩ := hL
        exact ⟨K, hK, subset_rfl⟩)

/-- The family of all compact open subgroups normal in the prescribed compact. -/
def compactOpenNormalFamily (K0 : Subgroup H) : Set (Subgroup H) :=
  {K | K ≤ K0 ∧ (K.subgroupOf K0).Normal ∧ IsOpen (K : Set H) ∧ IsCompact (K : Set H)}

/-- A compact open subgroup has a normal compact-open identity basis in the
ambient totally disconnected group. -/
theorem exists_compactOpenNormalBasis [TotallyDisconnectedSpace H]
    (K0 : Subgroup H) (hcompact : IsCompact (K0 : Set H))
    (hopen : IsOpen (K0 : Set H)) :
    ∃ B : Set (Subgroup H), CompactOpenNormalBasis K0 B := by
  let B := compactOpenNormalFamily K0
  refine ⟨B, fun K hK => hK, ?_⟩
  have : CompactSpace K0 := isCompact_iff_compactSpace.mp hcompact
  refine hasBasis_iff.mpr ?_
  intro U
  constructor
  · intro hU
    obtain ⟨V, hVU, hVopen, h1V⟩ := mem_nhds_iff.mp hU
    obtain ⟨L, hL⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (hVopen.preimage (continuous_subtype_val : Continuous K0.subtype)) h1V
    let K : Subgroup H := L.toSubgroup.map K0.subtype
    have hKK0 : K ≤ K0 := by
      rintro _ ⟨g, hg, rfl⟩
      exact g.property
    have hKnormal : (K.subgroupOf K0).Normal := by
      have heq : K.subgroupOf K0 = L.toSubgroup := by
        change (L.toSubgroup.map K0.subtype).comap K0.subtype = L.toSubgroup
        exact Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
      rw [heq]
      infer_instance
    have hKopen : IsOpen (K : Set H) :=
      hopen.isOpenEmbedding_subtypeVal.isOpenMap _ L.isOpen
    have hKcompact : IsCompact (K : Set H) :=
      (isCompact_univ : IsCompact (Set.univ : Set K0)).of_isClosed_subset
        L.isClosed (Set.subset_univ _) |>.image continuous_subtype_val
    refine ⟨K, ⟨hKK0, hKnormal, hKopen, hKcompact⟩, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    exact hVU (hL hg)
  · rintro ⟨K, hK, hKU⟩
    exact mem_of_superset (hK.2.2.1.mem_nhds K.one_mem) hKU

end Langlands.BruhatTits.SpecialCompact
