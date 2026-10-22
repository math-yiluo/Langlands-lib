import Langlands.Weil.Topology
import Mathlib.Topology.Algebra.Group.Neighborhood

/-! # The generic Weil pullback topology and its uniqueness -/

namespace Langlands.Weil

universe u

/-- The original pullback topology is the unique group topology inducing
the given topology on inertia and making its inclusion an open embedding. -/
theorem topologyProperties : TopologyProperties.{u} := by
  intro Γ _ _ _ φ
  have hkernel : IsOpen (inertiaSubgroup φ : Set (Pullback φ)) := by
    change IsOpen ((degree φ) ⁻¹' ({1} : Set Degree))
    exact (isOpen_discrete _).preimage (degree φ).continuous
  have hrange :
      Set.range (inertiaInclusion φ) = (inertiaSubgroup φ : Set (Pullback φ)) := by
    ext w
    constructor
    · rintro ⟨g, rfl⟩
      change degree φ (inertiaInclusion φ g) = 1
      rfl
    · intro hw
      have hn : w.val.2 = 1 := hw
      have hg : w.val.1 ∈ inertia φ := by
        change φ w.val.1 = 1
        have h := w.property
        change φ w.val.1 = frobenius w.val.2 at h
        simpa only [hn, map_one] using h
      refine ⟨⟨w.val.1, hg⟩, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact hn.symm
  have hembedding : Topology.IsEmbedding (inertiaInclusion φ) := by
    apply Topology.IsEmbedding.of_comp (inertiaInclusion φ).continuous
      (projection φ).continuous
    change Topology.IsEmbedding (Subtype.val : inertia φ → Γ)
    exact Topology.IsEmbedding.subtypeVal
  have hopen : Topology.IsOpenEmbedding (inertiaInclusion φ) :=
    ⟨hembedding, hrange.symm ▸ hkernel⟩
  have hgroup : IsTopologicalGroup (Pullback φ) := inferInstance
  have horiginal := hopen.map_nhds_eq (1 : inertia φ)
  refine ⟨hgroup, hopen, hkernel, ?_⟩
  intro t ht hi
  apply IsTopologicalGroup.ext ht hgroup
  have hnew := hi.map_nhds_eq (1 : inertia φ)
  simpa only [map_one] using hnew.symm.trans horiginal

end Langlands.Weil
