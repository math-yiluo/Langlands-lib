import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Cocompactness through an open homomorphism

If an open homomorphism of topological groups has its kernel inside a closed subgroup `K`
of a locally compact group, and sends `K` into a compact set, then `K` is compact modulo
every subgroup containing that kernel.
-/

open Set Topology

namespace Langlands.BruhatTits.RationalPoints

variable {G T : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] [Group T] [TopologicalSpace T] [IsTopologicalGroup T]

/-- A compact subset of the closed subgroup `K` meets every kernel coset contained in `K`. -/
theorem exists_isCompact_ker_coset_of_isOpenMap
    (q : G →* T) (hq : IsOpenMap q) (K : Subgroup G) (hK : IsClosed (K : Set G))
    (hker : q.ker ≤ K) {C₀ : Set T} (hC₀ : IsCompact C₀) (hKC₀ : q '' K ⊆ C₀) :
    ∃ C ⊆ (K : Set G), IsCompact C ∧ ∀ k ∈ K, ∃ c ∈ C, c⁻¹ * k ∈ q.ker := by
  obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds (1 : G)
  have h1 : (1 : G) ∈ interior N := mem_interior_iff_mem_nhds.2 hN
  have hrange : IsClosed (q.range : Set T) := by
    apply Subgroup.isClosed_of_isOpen
    rw [MonoidHom.coe_range]
    exact hq.isOpen_range
  have hS : IsCompact (C₀ ∩ q.range) := hC₀.inter_right hrange
  have hcover : C₀ ∩ q.range ⊆ ⋃ g : G, q '' ((g * ·) '' interior N) := by
    rintro t ⟨-, g, rfl⟩
    exact mem_iUnion.2 ⟨g, mem_image_of_mem q ⟨1, h1, mul_one g⟩⟩
  obtain ⟨s, hs⟩ := hS.elim_finite_subcover (fun g : G => q '' ((g * ·) '' interior N))
    (fun g => hq _ (isOpenMap_mul_left g _ isOpen_interior)) hcover
  refine ⟨(⋃ g ∈ s, (g * ·) '' N) ∩ K, inter_subset_right,
    (s.isCompact_biUnion fun g _ => hNc.image (continuous_const.mul continuous_id)).inter_right hK, ?_⟩
  intro k hk
  have hqk : q k ∈ C₀ ∩ q.range := ⟨hKC₀ (mem_image_of_mem q hk), k, rfl⟩
  obtain ⟨g, hg, hkg⟩ := mem_iUnion₂.1 (hs hqk)
  obtain ⟨c, ⟨u, hu, rfl⟩, hc⟩ := hkg
  have hck : (g * u)⁻¹ * k ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hc, inv_mul_cancel]
  refine ⟨g * u, ⟨mem_iUnion₂.2 ⟨g, hg, u, interior_subset hu, rfl⟩, ?_⟩, hck⟩
  have := K.mul_mem hk (K.inv_mem (hker hck))
  simpa using this

/-- Cocompactness of a closed subgroup modulo a subgroup containing the kernel of an open
homomorphism that maps the closed subgroup into a compact set. -/
theorem compactSpace_quotient_subgroupOf_of_isOpenMap
    (q : G →* T) (hq : IsOpenMap q) (K H : Subgroup G) (hK : IsClosed (K : Set G))
    (hkerK : q.ker ≤ K) (hkerH : q.ker ≤ H) {C₀ : Set T} (hC₀ : IsCompact C₀)
    (hKC₀ : q '' K ⊆ C₀) :
    CompactSpace (K ⧸ H.subgroupOf K) := by
  obtain ⟨C, hCK, hC, hcos⟩ :=
    exists_isCompact_ker_coset_of_isOpenMap q hq K hK hkerK hC₀ hKC₀
  have hC' : IsCompact (((↑) : K → G) ⁻¹' C) := by
    rw [IsInducing.subtypeVal.isCompact_preimage_iff (by simpa using hCK)]
    exact hC
  have himage : (QuotientGroup.mk : K → K ⧸ H.subgroupOf K) '' (((↑) : K → G) ⁻¹' C) =
      univ := by
    refine eq_univ_of_forall fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H k =>
      obtain ⟨c, hc, hck⟩ := hcos k k.2
      refine ⟨⟨c, hCK hc⟩, hc, ?_⟩
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      exact hkerH (by simpa using hck)
  exact ⟨himage ▸ hC'.image QuotientGroup.continuous_mk⟩

end Langlands.BruhatTits.RationalPoints
