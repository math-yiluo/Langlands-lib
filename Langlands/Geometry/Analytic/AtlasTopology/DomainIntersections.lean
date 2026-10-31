import Langlands.Geometry.Analytic.AtlasTopology.RefinementComposition
import Langlands.Geometry.Analytic.AtlasTopology.Restriction

/-! # Intersections of subspaces covered by contained net members -/

universe u

namespace Langlands.Analytic.AtlasTopology

open Set Filter
open scoped Topology

variable {X : Type u}

/-- The family of intersections of one member of each family. -/
def intersectionFamily (τ υ : Set (Set X)) : Set (Set X) :=
  {W | ∃ U ∈ τ, ∃ V ∈ υ, W = U ∩ V}

@[simp]
theorem intersectionFamily_singletons (S T : Set X) :
    intersectionFamily {S} {T} = {S ∩ T} := by
  ext W
  simp [intersectionFamily]

variable [TopologicalSpace X]

/-- A quasinet on an actual subspace is exactly a finite relative local
refinement of that subspace by original members. -/
theorem isQuasinet_restrictedFamily_iff (τ : Set (Set X)) (S : Set X) :
    IsQuasinet (restrictedFamily τ S) ↔ LocallyRefines τ {S} := by
  constructor
  · intro h U hU x hx
    have hUS : U = S := mem_singleton_iff.mp hU
    subst U
    obtain ⟨σ, hf, hs, hm, hn⟩ := h ⟨x, hx⟩
    let δ : Set (Set X) := (fun W : Set S => Subtype.val '' W) '' σ
    refine ⟨δ, hf.image _, ?_, ?_, ?_⟩
    · rintro V ⟨W, hW, rfl⟩
      obtain ⟨V, hV, hVS, rfl⟩ := hs hW
      simpa only [Subtype.image_preimage_val, inter_eq_right.mpr hVS] using hV
    · rintro V ⟨W, hW, rfl⟩
      exact ⟨fun _ ⟨y, _, hy⟩ => hy ▸ y.property, ⟨⟨x, hx⟩, hm W hW, rfl⟩⟩
    · rw [← map_nhds_subtype_val (⟨x, hx⟩ : S)]
      change Subtype.val ⁻¹' ⋃₀ δ ∈ 𝓝 (⟨x, hx⟩ : S)
      apply Filter.mem_of_superset hn
      rintro y ⟨W, hW, hy⟩
      exact ⟨_, ⟨W, hW, rfl⟩, ⟨y, hy, rfl⟩⟩
  · intro h x
    obtain ⟨σ, hf, hs, hm, hn⟩ := h S (mem_singleton S) x.val x.property
    let δ : Set (Set S) := (fun V : Set X => (Subtype.val ⁻¹' V : Set S)) '' σ
    refine ⟨δ, hf.image _, ?_, ?_, ?_⟩
    · rintro W ⟨V, hV, rfl⟩
      exact ⟨V, hs hV, (hm V hV).1, rfl⟩
    · rintro W ⟨V, hV, rfl⟩
      exact (hm V hV).2
    · rw [← map_nhds_subtype_val x] at hn
      change Subtype.val ⁻¹' ⋃₀ σ ∈ 𝓝 x at hn
      apply Filter.mem_of_superset hn
      rintro y ⟨V, hV, hy⟩
      exact ⟨_, ⟨V, hV, rfl⟩, hy⟩

/-- Intersect the two finite relative neighborhood witnesses. -/
theorem LocallyRefines.intersectionFamily {τ υ κ η : Set (Set X)}
    (hτ : LocallyRefines τ κ) (hυ : LocallyRefines υ η) :
    LocallyRefines (intersectionFamily τ υ) (intersectionFamily κ η) := by
  rintro W ⟨S, hS, T, hT, rfl⟩ x hx
  obtain ⟨σ, hfσ, hsσ, hmσ, hnσ⟩ := hτ S hS x hx.1
  obtain ⟨ρ, hfρ, hsρ, hmρ, hnρ⟩ := hυ T hT x hx.2
  let δ : Set (Set X) :=
    (fun p : Set X × Set X => p.1 ∩ p.2) '' (σ ×ˢ ρ)
  refine ⟨δ, (hfσ.prod hfρ).image _, ?_, ?_, ?_⟩
  · rintro V ⟨⟨U, W⟩, ⟨hU, hW⟩, rfl⟩
    exact ⟨U, hsσ hU, W, hsρ hW, rfl⟩
  · rintro V ⟨⟨U, W⟩, ⟨hU, hW⟩, rfl⟩
    exact ⟨inter_subset_inter (hmσ U hU).1 (hmρ W hW).1,
      (hmσ U hU).2, (hmρ W hW).2⟩
  · have heq : ⋃₀ δ = (⋃₀ σ) ∩ ⋃₀ ρ := by
      ext y
      constructor
      · rintro ⟨_, ⟨⟨U, V⟩, ⟨hU, hV⟩, rfl⟩, hy⟩
        exact ⟨⟨U, hU, hy.1⟩, ⟨V, hV, hy.2⟩⟩
      · rintro ⟨⟨U, hU, hyU⟩, ⟨V, hV, hyV⟩⟩
        exact ⟨_, ⟨(U, V), ⟨hU, hV⟩, rfl⟩, hyU, hyV⟩
    rw [heq]
    exact inter_mem ((nhdsWithin_mono x inter_subset_left) hnσ)
      ((nhdsWithin_mono x inter_subset_right) hnρ)

/-- The net intersection axiom supplies finite relative refinements of
each member intersection by members of the original family. -/
theorem IsNet.locallyRefines_intersectionFamily {τ : Set (Set X)} (hτ : IsNet τ) :
    LocallyRefines τ (intersectionFamily τ τ) := by
  rintro W ⟨U, hU, V, hV, rfl⟩ x hx
  exact (isQuasinet_restrictedFamily_iff τ (U ∩ V)).mp (hτ.2 U hU V hV)
    (U ∩ V) (mem_singleton _) x hx

/-- Subspaces locally covered by contained members are closed under
intersection. No compactness or separation assumption is needed. -/
theorem IsNet.isQuasinet_restrictedFamily_inter {τ : Set (Set X)} (hτ : IsNet τ)
    {S T : Set X} (hS : IsQuasinet (restrictedFamily τ S))
    (hT : IsQuasinet (restrictedFamily τ T)) :
    IsQuasinet (restrictedFamily τ (S ∩ T)) := by
  apply (isQuasinet_restrictedFamily_iff τ (S ∩ T)).mpr
  have h := ((isQuasinet_restrictedFamily_iff τ S).mp hS).intersectionFamily
    ((isQuasinet_restrictedFamily_iff τ T).mp hT)
  rw [intersectionFamily_singletons] at h
  exact h.trans hτ.locallyRefines_intersectionFamily

/-- The entire induced net on an intersection is constructed, rather than
assumed as part of the subspace input. -/
theorem IsNet.restrict_inter {τ : Set (Set X)} (hτ : IsNet τ)
    {S T : Set X} (hS : IsQuasinet (restrictedFamily τ S))
    (hT : IsQuasinet (restrictedFamily τ T)) :
    IsNet (restrictedFamily τ (S ∩ T)) :=
  hτ.restrict (S ∩ T) (hτ.isQuasinet_restrictedFamily_inter hS hT)

end Langlands.Analytic.AtlasTopology
