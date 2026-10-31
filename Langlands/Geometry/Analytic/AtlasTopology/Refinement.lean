import Langlands.Geometry.Analytic.AtlasTopology.Definitions
import Mathlib.Topology.ContinuousOn

/-! # Relative finite local refinements of nets -/

universe u

namespace Langlands.Analytic.AtlasTopology

open Set Filter
open scoped Topology

variable {X : Type u} [TopologicalSpace X]

/-- Each old member has, at every one of its points, a finite relative
neighborhood made of new members contained in the old member and containing
that point. -/
def LocallyRefines (υ τ : Set (Set X)) : Prop :=
  ∀ U ∈ τ, ∀ x ∈ U, ∃ σ : Set (Set X),
    σ.Finite ∧ σ ⊆ υ ∧ (∀ V ∈ σ, V ⊆ U ∧ x ∈ V) ∧ ⋃₀ σ ∈ 𝓝[U] x

theorem LocallyRefines.refl (τ : Set (Set X)) : LocallyRefines τ τ := by
  intro U hU x hx
  refine ⟨{U}, finite_singleton U, singleton_subset_iff.mpr hU, ?_, ?_⟩
  · intro V hV
    rcases mem_singleton_iff.mp hV with rfl
    exact ⟨Subset.rfl, hx⟩
  · simpa only [sUnion_singleton] using (self_mem_nhdsWithin : U ∈ 𝓝[U] x)

/-- A finite union of relative finite neighborhood refinements refines
the original finite ambient neighborhood. -/
theorem IsQuasinet.refine {τ υ : Set (Set X)} (hτ : IsQuasinet τ)
    (h : LocallyRefines υ τ) : IsQuasinet υ := by
  classical
  intro x
  obtain ⟨ξ, hξ, hξτ, hxξ, hnξ⟩ := hτ x
  have hw : ∀ U : ξ, ∃ σ : Set (Set X),
      σ.Finite ∧ σ ⊆ υ ∧ (∀ V ∈ σ, V ⊆ U.val ∧ x ∈ V) ∧
        ⋃₀ σ ∈ 𝓝[U.val] x :=
    fun U => h U.val (hξτ U.property) x (hxξ U.val U.property)
  choose σ hf hs hx hn using hw
  let : Fintype ξ := hξ.fintype
  let δ : Set (Set X) := ⋃ U : ξ, σ U
  refine ⟨δ, finite_iUnion hf, ?_, ?_, ?_⟩
  · intro V hV
    obtain ⟨U, hVU⟩ := mem_iUnion.mp hV
    exact hs U hVU
  · intro V hV
    obtain ⟨U, hVU⟩ := mem_iUnion.mp hV
    exact (hx U V hVU).2
  · rw [← nhdsWithin_eq_nhds.mpr hnξ, nhdsWithin_sUnion hξ x]
    apply Filter.mem_iSup.mpr
    intro U
    apply Filter.mem_iSup.mpr
    intro hU
    apply Filter.mem_of_superset (hn ⟨U, hU⟩)
    rintro y ⟨V, hV, hy⟩
    exact ⟨V, mem_iUnion.mpr ⟨⟨U, hU⟩, hV⟩, hy⟩

/-- Relative local refinements pass to every actual contained-member family. -/
theorem LocallyRefines.restrict {τ υ : Set (Set X)}
    (h : LocallyRefines υ τ) (S : Set X) :
    LocallyRefines (restrictedFamily υ S) (restrictedFamily τ S) := by
  rintro W ⟨U, hU, hUS, rfl⟩ x hx
  obtain ⟨σ, hf, hs, hxσ, hn⟩ := h U hU x.val hx
  let σ' : Set (Set S) := (fun V : Set X => (Subtype.val ⁻¹' V : Set S)) '' σ
  refine ⟨σ', hf.image _, ?_, ?_, ?_⟩
  · rintro V ⟨T, hT, rfl⟩
    exact ⟨T, hs hT, (hxσ T hT).1.trans hUS, rfl⟩
  · rintro V ⟨T, hT, rfl⟩
    exact ⟨preimage_mono (hxσ T hT).1, (hxσ T hT).2⟩
  · have heq : ⋃₀ σ' = (Subtype.val ⁻¹' ⋃₀ σ : Set S) := by
      ext y
      constructor
      · rintro ⟨V, ⟨T, hT, rfl⟩, hy⟩
        exact ⟨T, hT, hy⟩
      · rintro ⟨T, hT, hy⟩
        exact ⟨_, ⟨T, hT, rfl⟩, hy⟩
    rw [heq]
    have hc : Tendsto (Subtype.val : S → X)
        (𝓝[Subtype.val ⁻¹' U] x) (𝓝[U] x.val) :=
      continuous_subtype_val.continuousWithinAt.tendsto_nhdsWithin (fun _ hy => hy)
    exact hc hn

/-- Deleting members preserves the net when the remaining members have finite
relative neighborhood refinements inside every original member. -/
theorem IsNet.of_locallyRefines {τ υ : Set (Set X)} (hτ : IsNet τ)
    (hsub : υ ⊆ τ) (h : LocallyRefines υ τ) : IsNet υ := by
  refine ⟨hτ.1.refine h, ?_⟩
  intro U hU V hV
  exact (hτ.2 U (hsub hU) V (hsub hV)).refine (h.restrict (U ∩ V))

end Langlands.Analytic.AtlasTopology
