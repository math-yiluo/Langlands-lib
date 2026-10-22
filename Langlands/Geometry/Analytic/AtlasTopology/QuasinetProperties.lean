import Langlands.Geometry.Analytic.AtlasTopology.Definitions

/-! # Topology determined by a quasinet -/

universe u v

namespace Langlands.Analytic.AtlasTopology

open Set Filter
open scoped Topology

variable {X : Type u} [TopologicalSpace X] {τ : Set (Set X)}

theorem IsQuasinet.covers (hτ : IsQuasinet τ) : ⋃₀ τ = univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨σ, _, hστ, _, hxσ⟩ := hτ x
  obtain ⟨V, hVσ, hxV⟩ := Set.mem_sUnion.mp (mem_of_mem_nhds hxσ)
  exact Set.mem_sUnion.mpr ⟨V, hστ hVσ, hxV⟩

theorem IsQuasinet.mono (hτ : IsQuasinet τ) {υ : Set (Set X)}
    (hτυ : τ ⊆ υ) : IsQuasinet υ := by
  intro x
  obtain ⟨σ, hσ, hστ, hx, hn⟩ := hτ x
  exact ⟨σ, hσ, hστ.trans hτυ, hx, hn⟩

/-- A single chart covering the space gives a quasinet. -/
theorem isQuasinet_of_univ_mem (h : univ ∈ τ) : IsQuasinet τ := by
  intro x
  refine ⟨{univ}, Set.finite_singleton _, ?_, ?_, ?_⟩
  · simpa using h
  · simp
  · simp

/-- The singleton whole-space family is a net. This applies in particular
to the topology of each actual affinoid spectrum. -/
theorem isNet_singleton_univ : IsNet ({univ} : Set (Set X)) := by
  refine ⟨isQuasinet_of_univ_mem (by simp), ?_⟩
  intro U hU V hV
  simp only [Set.mem_singleton_iff] at hU hV
  subst U
  subst V
  apply isQuasinet_of_univ_mem
  refine ⟨univ, by simp, by simp, ?_⟩
  simp

/-- Continuity on the members implies continuity, using the finite
neighborhood union at each point. -/
theorem IsQuasinet.continuous {Y : Type v} [TopologicalSpace Y]
    (hτ : IsQuasinet τ) {f : X → Y}
    (hf : ∀ V ∈ τ, ContinuousOn f V) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨σ, hσ, hστ, hx, hn⟩ := hτ x
  have h : ContinuousWithinAt f (⋃₀ σ) x := by
    rw [ContinuousWithinAt, nhdsWithin_sUnion hσ]
    exact tendsto_iSup.mpr fun V => tendsto_iSup.mpr fun hV =>
      hf V (hστ hV) x (hx V hV)
  exact h.continuousAt hn

/-- Lemma 1.1.1(i), expressed through Mathlib's generated-topology predicate. -/
theorem IsQuasinet.isCoherentWith (hτ : IsQuasinet τ) :
    Topology.IsCoherentWith τ :=
  Topology.IsCoherentWith.of_continuous_prop fun _ hf => hτ.continuous hf

theorem IsQuasinet.isOpen_iff (hτ : IsQuasinet τ) (U : Set X) :
    IsOpen U ↔ ∀ V ∈ τ, IsOpen (Subtype.val ⁻¹' U : Set V) :=
  hτ.isCoherentWith.isOpen_iff

theorem IsQuasinet.isClosed_iff (hτ : IsQuasinet τ) (U : Set X) :
    IsClosed U ↔ ∀ V ∈ τ, IsClosed (Subtype.val ⁻¹' U : Set V) :=
  hτ.isCoherentWith.isClosed_iff

theorem IsQuasinet.continuous_iff {Y : Type v} [TopologicalSpace Y]
    (hτ : IsQuasinet τ) (f : X → Y) :
    Continuous f ↔ ∀ V ∈ τ, ContinuousOn f V :=
  hτ.isCoherentWith.continuous_iff

/-- Finite witness families multiply to a witness family of rectangles. -/
theorem IsQuasinet.product {Y : Type v} [TopologicalSpace Y]
    {υ : Set (Set Y)} (hτ : IsQuasinet τ) (hυ : IsQuasinet υ) :
    IsQuasinet (productFamily τ υ) := by
  intro x
  obtain ⟨σ, hσ, hστ, hxσ, hnσ⟩ := hτ x.1
  obtain ⟨ρ, hρ, hρυ, hxρ, hnρ⟩ := hυ x.2
  let ξ : Set (Set (X × Y)) :=
    (fun p : Set X × Set Y => p.1 ×ˢ p.2) '' (σ ×ˢ ρ)
  refine ⟨ξ, (hσ.prod hρ).image _, ?_, ?_, ?_⟩
  · rintro W ⟨⟨U, V⟩, ⟨hU, hV⟩, rfl⟩
    exact ⟨U, hστ hU, V, hρυ hV, rfl⟩
  · rintro W ⟨⟨U, V⟩, ⟨hU, hV⟩, rfl⟩
    exact ⟨hxσ U hU, hxρ V hV⟩
  · have hξ : ⋃₀ ξ = (⋃₀ σ) ×ˢ (⋃₀ ρ) := by
      ext z
      constructor
      · rintro ⟨W, ⟨⟨U, V⟩, ⟨hU, hV⟩, rfl⟩, hz⟩
        exact ⟨⟨U, hU, hz.1⟩, ⟨V, hV, hz.2⟩⟩
      · rintro ⟨⟨U, hU, hzU⟩, ⟨V, hV, hzV⟩⟩
        exact ⟨U ×ˢ V, ⟨(U, V), ⟨hU, hV⟩, rfl⟩, hzU, hzV⟩
    rw [hξ]
    exact prod_mem_nhds hnσ hnρ

/-- Lemma 1.1.1(ii): compact intersections detect Hausdorffness of the
ambient space when each quasinet member is compact Hausdorff. -/
theorem IsQuasinet.t2Space_iff (hτ : IsQuasinet τ) (hc : IsCompactFamily τ) :
    T2Space X ↔ ∀ U ∈ τ, ∀ V ∈ τ, IsCompact (U ∩ V) := by
  constructor
  · intro h U hU V hV
    let := h
    exact (hc U hU).1.inter (hc V hV).1
  · intro h
    apply t2_iff_isClosed_diagonal.mpr
    apply ((hτ.product hτ).isClosed_iff (Set.diagonal X)).mpr
    rintro W ⟨U, hU, V, hV, rfl⟩
    let := (hc U hU).2
    let := (hc V hV).2
    let : CompactSpace ↥(U ∩ V) := isCompact_iff_compactSpace.mp (h U hU V hV)
    let d : ↥(U ∩ V) → U × V :=
      fun z => (⟨z.1, z.2.1⟩, ⟨z.1, z.2.2⟩)
    have hd : Continuous d :=
      (continuous_subtype_val.subtype_mk _).prodMk (continuous_subtype_val.subtype_mk _)
    have hclosed := (isCompact_range hd).isClosed
    have heq : Subtype.val ⁻¹' Set.diagonal X =
        (Homeomorph.Set.prod U V) ⁻¹' Set.range d := by
      ext z
      change z.1.1 = z.1.2 ↔ ∃ a, d a = (Homeomorph.Set.prod U V) z
      constructor
      · intro hz
        refine ⟨⟨z.1.1, z.2.1, hz.symm ▸ z.2.2⟩, ?_⟩
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          exact hz
      · rintro ⟨a, ha⟩
        have h₁ := congrArg (fun p : U × V => p.1.1) ha
        have h₂ := congrArg (fun p : U × V => p.2.1) ha
        exact h₁.symm.trans h₂
    rw [heq]
    exact hclosed.preimage (Homeomorph.Set.prod U V).continuous

/-- Finite compact unions give genuine compact neighborhoods. -/
theorem IsQuasinet.weaklyLocallyCompactSpace (hτ : IsQuasinet τ)
    (hc : ∀ V ∈ τ, IsCompact V) : WeaklyLocallyCompactSpace X where
  exists_compact_mem_nhds x := by
    obtain ⟨σ, hσ, hστ, _, hn⟩ := hτ x
    exact ⟨⋃₀ σ, hσ.isCompact_sUnion (fun V hV => hc V (hστ hV)), hn⟩

/-- The local compactness remark following Lemma 1.1.1. -/
theorem IsQuasinet.locallyCompactSpace [T2Space X] (hτ : IsQuasinet τ)
    (hc : ∀ V ∈ τ, IsCompact V) : LocallyCompactSpace X := by
  let := hτ.weaklyLocallyCompactSpace hc
  infer_instance

end Langlands.Analytic.AtlasTopology
