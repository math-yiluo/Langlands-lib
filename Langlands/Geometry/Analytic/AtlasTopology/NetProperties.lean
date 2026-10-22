import Langlands.Geometry.Analytic.AtlasTopology.QuasinetProperties
import Mathlib.Topology.LocallyClosed

/-! # Compact nets and their intersections -/

universe u v

namespace Langlands.Analytic.AtlasTopology

open Set Filter
open scoped Topology

variable {X : Type u} [TopologicalSpace X]

/-- A subspace with compact neighborhoods is locally closed in any Hausdorff
space in which it is embedded. The ambient space need not be locally compact. -/
theorem isLocallyClosed_range_of_isEmbedding
    {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [WeaklyLocallyCompactSpace X] {f : X → Y} (hf : Topology.IsEmbedding f) :
    IsLocallyClosed (Set.range f) := by
  rw [isLocallyClosed_iff_isLocallyClosedAt]
  rintro _ ⟨x, rfl⟩
  obtain ⟨K, hK, hn⟩ := exists_compact_mem_nhds x
  rw [hf.isInducing.nhds_eq_comap] at hn
  obtain ⟨U, hU, hUK⟩ := hn
  apply isLocallyClosedAt_iff_exists_isClosed_eventuallyEqSet.mpr
  refine ⟨f '' K, (hK.image hf.continuous).isClosed, ?_⟩
  filter_upwards [hU] with y hy
  apply propext
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, hUK hy, rfl⟩
  · rintro ⟨z, _, rfl⟩
    exact ⟨z, rfl⟩

/-- Compactness of a contained member is preserved by the induced topology
on the containing subspace. -/
theorem isCompact_restrictedFamily {τ : Set (Set X)}
    (hc : ∀ V ∈ τ, IsCompact V) (Y : Set X) :
    ∀ W ∈ restrictedFamily τ Y, IsCompact W := by
  rintro W ⟨V, hV, hVY, rfl⟩
  apply Subtype.isCompact_iff.mpr
  have heq : Subtype.val '' (Subtype.val ⁻¹' V : Set Y) = V := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hx
      exact ⟨⟨x, hVY hx⟩, hx, rfl⟩
  rw [heq]
  exact hc V hV

/-- The net axiom supplies the actual quasinet on each intersection;
compactness of its members gives local compactness there. -/
theorem IsNet.locallyCompactSpace_inter {τ : Set (Set X)}
    (hτ : IsNet τ) (hc : IsCompactFamily τ)
    {U V : Set X} (hU : U ∈ τ) (hV : V ∈ τ) :
    LocallyCompactSpace ↥(U ∩ V) := by
  let := (hc U hU).2
  let : T2Space ↥(U ∩ V) :=
    (Topology.IsEmbedding.inclusion (inter_subset_left : U ∩ V ⊆ U)).t2Space
  exact (hτ.2 U hU V hV).locallyCompactSpace
    (isCompact_restrictedFamily (fun W hW => (hc W hW).1) (U ∩ V))

/-- Berkovich 1993, Lemma 1.1.2(i), in the first member's subspace topology. -/
theorem IsNet.isLocallyClosed_inter_left {τ : Set (Set X)}
    (hτ : IsNet τ) (hc : IsCompactFamily τ)
    {U V : Set X} (hU : U ∈ τ) (hV : V ∈ τ) :
    IsLocallyClosed (Subtype.val ⁻¹' V : Set U) := by
  let := (hc U hU).2
  let := hτ.locallyCompactSpace_inter hc hU hV
  let e := Set.inclusion (inter_subset_left : U ∩ V ⊆ U)
  have h := isLocallyClosed_range_of_isEmbedding
    (Topology.IsEmbedding.inclusion (inter_subset_left : U ∩ V ⊆ U))
  have heq : Set.range e = (Subtype.val ⁻¹' V : Set U) := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact z.2.2
    · intro hx
      exact ⟨⟨x.1, x.2, hx⟩, rfl⟩
  rwa [heq] at h

/-- The same conclusion in the second member, without ambient Hausdorffness. -/
theorem IsNet.isLocallyClosed_inter_right {τ : Set (Set X)}
    (hτ : IsNet τ) (hc : IsCompactFamily τ)
    {U V : Set X} (hU : U ∈ τ) (hV : V ∈ τ) :
    IsLocallyClosed (Subtype.val ⁻¹' U : Set V) :=
  hτ.isLocallyClosed_inter_left hc hV hU

end Langlands.Analytic.AtlasTopology
