import Langlands.Geometry.Analytic.AtlasTopology.DomainIntersections

/-! # Intersecting two nets on the same topological space -/

universe u

namespace Langlands.Analytic.AtlasTopology

open Set Filter
open scoped Topology

variable {X : Type u} [TopologicalSpace X]

/-- Intersect the finite neighborhood witnesses of two quasinets. -/
theorem IsQuasinet.intersectionFamily {τ υ : Set (Set X)}
    (hτ : IsQuasinet τ) (hυ : IsQuasinet υ) :
    IsQuasinet (intersectionFamily τ υ) := by
  intro x
  obtain ⟨σ, hfσ, hsσ, hmσ, hnσ⟩ := hτ x
  obtain ⟨ρ, hfρ, hsρ, hmρ, hnρ⟩ := hυ x
  let δ : Set (Set X) :=
    (fun p : Set X × Set X => p.1 ∩ p.2) '' (σ ×ˢ ρ)
  refine ⟨δ, (hfσ.prod hfρ).image _, ?_, ?_, ?_⟩
  · rintro W ⟨⟨U, V⟩, ⟨hU, hV⟩, rfl⟩
    exact ⟨U, hsσ hU, V, hsρ hV, rfl⟩
  · rintro W ⟨⟨U, V⟩, ⟨hU, hV⟩, rfl⟩
    exact ⟨hmσ U hU, hmρ V hV⟩
  · have heq : ⋃₀ δ = (⋃₀ σ) ∩ ⋃₀ ρ := by
      ext y
      constructor
      · rintro ⟨_, ⟨⟨U, V⟩, ⟨hU, hV⟩, rfl⟩, hy⟩
        exact ⟨⟨U, hU, hy.1⟩, ⟨V, hV, hy.2⟩⟩
      · rintro ⟨⟨U, hU, hyU⟩, ⟨V, hV, hyV⟩⟩
        exact ⟨_, ⟨(U, V), ⟨hU, hV⟩, rfl⟩, hyU, hyV⟩
    rw [heq]
    exact inter_mem hnσ hnρ

/-- The intersections of one member from each of two nets form a net. -/
theorem IsNet.intersectionFamily {τ υ : Set (Set X)}
    (hτ : IsNet τ) (hυ : IsNet υ) :
    IsNet (intersectionFamily τ υ) := by
  refine ⟨hτ.1.intersectionFamily hυ.1, ?_⟩
  rintro _ ⟨U, hU, V, hV, rfl⟩ _ ⟨U', hU', V', hV', rfl⟩
  apply (isQuasinet_restrictedFamily_iff _ _).mpr
  have h := ((isQuasinet_restrictedFamily_iff τ (U ∩ U')).mp
    (hτ.2 U hU U' hU')).intersectionFamily
    ((isQuasinet_restrictedFamily_iff υ (V ∩ V')).mp
      (hυ.2 V hV V' hV'))
  rw [intersectionFamily_singletons] at h
  rwa [inter_inter_inter_comm U V U' V']

/-- The actual binary intersection operation on families equipped with a net proof. -/
def intersectionNet (τ υ : {σ : Set (Set X) // IsNet σ}) :
    {σ : Set (Set X) // IsNet σ} :=
  ⟨intersectionFamily τ.val υ.val, τ.property.intersectionFamily υ.property⟩

@[simp]
theorem intersectionNet_val (τ υ : {σ : Set (Set X) // IsNet σ}) :
    (intersectionNet τ υ).val = intersectionFamily τ.val υ.val := rfl

end Langlands.Analytic.AtlasTopology
