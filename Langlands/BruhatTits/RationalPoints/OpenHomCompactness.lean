import Langlands.BruhatTits.RationalPoints.OpenHomCocompactness
import Mathlib.Topology.Algebra.Group.Pointwise

/-! # Compactness through an open homomorphism -/

open Set Topology
open scoped Pointwise

namespace Langlands.BruhatTits.RationalPoints

variable {G T : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] [Group T] [TopologicalSpace T] [IsTopologicalGroup T]
  [CompactSpace T]

/-- A locally compact group with compact kernel under an open homomorphism into a
compact group is compact. Surjectivity and continuity of the homomorphism are not required. -/
theorem compactSpace_of_isOpenMap_of_isCompact_ker
    (q : G →* T) (hq : IsOpenMap q) (hker : IsCompact (q.ker : Set G)) :
    CompactSpace G := by
  obtain ⟨C, _, hC, hcos⟩ :=
    exists_isCompact_ker_coset_of_isOpenMap q hq ⊤
      (by simp) le_top isCompact_univ
      (by simp)
  have hcover : C * (q.ker : Set G) = univ := by
    apply eq_univ_of_forall
    intro g
    obtain ⟨c, hc, hcg⟩ := hcos g (by simp)
    exact ⟨c, hc, c⁻¹ * g, hcg, by simp⟩
  exact ⟨hcover ▸ hC.mul hker⟩

/-- An open subgroup is compact if its intersection with the kernel of an open
homomorphism into a compact group is compact. -/
theorem isCompact_subgroup_of_isOpenMap_of_isCompact_inf_ker
    (q : G →* T) (hq : IsOpenMap q) (H : Subgroup G) (hH : IsOpen (H : Set G))
    (hker : IsCompact ((H ⊓ q.ker : Subgroup G) : Set G)) :
    IsCompact (H : Set G) := by
  have hHclosed : IsClosed (H : Set G) := H.isClosed_of_isOpen hH
  let : WeaklyLocallyCompactSpace H := hHclosed.weaklyLocallyCompactSpace
  have hqH : IsOpenMap (q.comp H.subtype) := hq.comp hH.isOpenMap_subtype_val
  have hkerH : IsCompact ((q.comp H.subtype).ker : Set H) := by
    have heq : ((q.comp H.subtype).ker : Set H) =
        (Subtype.val : H → G) ⁻¹' ((H ⊓ q.ker : Subgroup G) : Set G) := by
      ext h
      simp
    rw [heq]
    exact hHclosed.isClosedEmbedding_subtypeVal.isCompact_preimage hker
  let : CompactSpace H := compactSpace_of_isOpenMap_of_isCompact_ker
    (q.comp H.subtype) hqH hkerH
  simpa using (isCompact_univ : IsCompact (univ : Set H)).image
    (continuous_subtype_val : Continuous (Subtype.val : H → G))

end Langlands.BruhatTits.RationalPoints
