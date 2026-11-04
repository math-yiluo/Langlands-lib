import Langlands.Geometry.Analytic.AtlasTopology.DomainIntersections
import Mathlib.Topology.Compactness.Compact

/-! # Finite covers of compact subsets by quasinet members -/

universe u

namespace Langlands.Analytic.AtlasTopology

open Set Filter
open scoped Topology

variable {X : Type u} [TopologicalSpace X]

/-- Compactness turns the finite neighborhood families in a quasinet into
a finite cover by members. No directedness or separation is required. -/
theorem IsQuasinet.exists_finite_cover_of_isCompact {τ : Set (Set X)}
    (hτ : IsQuasinet τ) {S : Set X} (hS : IsCompact S) :
    ∃ σ : Set (Set X), σ.Finite ∧ σ ⊆ τ ∧ S ⊆ ⋃₀ σ := by
  classical
  choose σ hf hs _ hn using hτ
  obtain ⟨t, _, ht⟩ := hS.elim_nhds_subcover (fun x => ⋃₀ σ x) (fun x _ => hn x)
  let δ : Set (Set X) := ⋃ x ∈ (t : Set X), σ x
  refine ⟨δ, t.finite_toSet.biUnion (fun x _ => hf x), ?_, ?_⟩
  · rintro V hV
    obtain ⟨x, _, hx⟩ := mem_iUnion₂.mp hV
    exact hs x hx
  · intro x hx
    obtain ⟨y, hy, V, hV, hxV⟩ := mem_iUnion₂.mp (ht hx)
    exact ⟨V, mem_iUnion₂.mpr ⟨y, hy, hV⟩, hxV⟩

/-- A quasinet of contained members covers each compact subset of the
subspace by finitely many of those original ambient members. -/
theorem exists_finite_cover_of_restrictedFamily
    {τ : Set (Set X)} {Y S : Set X}
    (hτ : IsQuasinet (restrictedFamily τ Y))
    (hS : IsCompact S) (hSY : S ⊆ Y) :
    ∃ σ : Set (Set X), σ.Finite ∧ σ ⊆ τ ∧
      (∀ V ∈ σ, V ⊆ Y) ∧ S ⊆ ⋃₀ σ := by
  have hc : IsCompact (Subtype.val ⁻¹' S : Set Y) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hS
      (by simpa only [Subtype.range_coe] using hSY)
  obtain ⟨σ, hf, hs, hcov⟩ := hτ.exists_finite_cover_of_isCompact hc
  let δ : Set (Set X) := (fun W : Set Y => Subtype.val '' W) '' σ
  have hmem {W : Set Y} (hW : W ∈ σ) :
      Subtype.val '' W ∈ τ ∧ Subtype.val '' W ⊆ Y := by
    obtain ⟨V, hV, hVY, rfl⟩ := hs hW
    simpa only [Subtype.image_preimage_val, inter_eq_right.mpr hVY] using
      (show V ∈ τ ∧ V ⊆ Y from ⟨hV, hVY⟩)
  refine ⟨δ, hf.image _, ?_, ?_, ?_⟩
  · rintro _ ⟨W, hW, rfl⟩
    exact (hmem hW).1
  · rintro _ ⟨W, hW, rfl⟩
    exact (hmem hW).2
  · intro x hx
    obtain ⟨W, hW, hxW⟩ := hcov (show (⟨x, hSY hx⟩ : Y) ∈ Subtype.val ⁻¹' S from hx)
    exact ⟨_, ⟨W, hW, rfl⟩, ⟨⟨x, hSY hx⟩, hxW, rfl⟩⟩

/-- The net intersection axiom gives finite covers of compact subsets of
two members by original members contained in both. -/
theorem IsNet.exists_finite_cover_of_subset_inter {τ : Set (Set X)}
    (hτ : IsNet τ) {U V S : Set X} (hU : U ∈ τ) (hV : V ∈ τ)
    (hS : IsCompact S) (hSUV : S ⊆ U ∩ V) :
    ∃ σ : Set (Set X), σ.Finite ∧ σ ⊆ τ ∧
      (∀ W ∈ σ, W ⊆ U ∩ V) ∧ S ⊆ ⋃₀ σ :=
  exists_finite_cover_of_restrictedFamily (hτ.2 U hU V hV) hS hSUV

end Langlands.Analytic.AtlasTopology
