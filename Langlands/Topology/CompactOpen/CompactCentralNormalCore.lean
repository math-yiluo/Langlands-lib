import Langlands.Topology.CompactOpen.NeighborhoodBasis
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.OpenSubgroup

open Set Topology

namespace Langlands

variable {G : Type*} [Group G] [TopologicalSpace G]
  [CompactSpace (G ⧸ Subgroup.center G)]

section TopologicalGroup

variable [IsTopologicalGroup G]

/-- The normal core of an open subgroup is open when the central quotient is compact. -/
def compactCentralNormalCore (K : OpenSubgroup G) : OpenSubgroup G where
  toSubgroup := K.toSubgroup.normalCore
  isOpen' := by
    let Z := Subgroup.center G
    have hZ : Z ≤ (MulAut.conj : G →* MulAut G).ker := by
      intro z hz
      change MulAut.conj z = 1
      ext x
      change z * x * z⁻¹ = x
      rw [(Subgroup.mem_center_iff.mp hz x).symm, mul_inv_cancel_right]
    let conj := QuotientGroup.lift Z MulAut.conj hZ
    let act : (G ⧸ Z) × G → G := fun p => conj p.1 p.2
    have hact : Continuous act := by
      rw [← (QuotientGroup.isOpenQuotientMap_mk.prodMap
        IsOpenQuotientMap.id).continuous_comp_iff]
      exact (continuous_fst.mul continuous_snd).mul continuous_fst.inv
    have hprod : (univ : Set (G ⧸ Z)) ×ˢ ({1} : Set G) ⊆ act ⁻¹' (K : Set G) := by
      rintro ⟨q, x⟩ ⟨_, hx⟩
      change x = 1 at hx
      subst x
      change conj q 1 ∈ K
      rw [map_one]
      exact K.one_mem
    obtain ⟨U, V, _, hV, hU, h1V, hUV⟩ :=
      generalized_tube_lemma isCompact_univ isCompact_singleton (K.isOpen.preimage hact) hprod
    apply K.toSubgroup.normalCore.isOpen_of_mem_nhds (g := 1)
    refine Filter.mem_of_superset (hV.mem_nhds (h1V (mem_singleton 1))) ?_
    intro x hx g
    exact hUV (a := ((g : G ⧸ Z), x)) ⟨hU (mem_univ _), hx⟩

@[simp]
theorem compactCentralNormalCore_toSubgroup (K : OpenSubgroup G) :
    (compactCentralNormalCore K).toSubgroup = K.toSubgroup.normalCore := rfl

/-- An open subgroup containing the center has finite index when the central quotient
is compact. -/
theorem finiteIndex_of_open_of_center_le {K : Subgroup G} (hK : IsOpen (K : Set G))
    (hZ : Subgroup.center G ≤ K) : K.FiniteIndex := by
  let f := Subgroup.quotientMapOfLE hZ
  have hsurj : Function.Surjective f := fun q =>
    QuotientGroup.induction_on q fun g => ⟨QuotientGroup.mk g, rfl⟩
  have hcont : Continuous f :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr QuotientGroup.continuous_mk
  let : CompactSpace (G ⧸ K) := hsurj.compactSpace hcont
  let : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK
  let : Finite (G ⧸ K) := finite_of_compact_of_discrete
  exact Subgroup.finiteIndex_of_finite_quotient

end TopologicalGroup

/-- Every identity neighborhood in a weakly locally compact nonarchimedean group with compact
central quotient contains a compact open normal subgroup. -/
theorem exists_compactOpenNormalSubgroup_subset [NonarchimedeanGroup G]
    [WeaklyLocallyCompactSpace G] {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ K : OpenSubgroup G, K.toSubgroup.Normal ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U := by
  obtain ⟨K, hKc, hKU⟩ := compactOpenSubgroupBasis G U hU
  let N := compactCentralNormalCore K
  have hNK : (N : Set G) ⊆ K := K.toSubgroup.normalCore_le
  exact ⟨N, K.toSubgroup.normalCore_normal, hKc.of_isClosed_subset N.isClosed hNK, hNK.trans hKU⟩

end Langlands
