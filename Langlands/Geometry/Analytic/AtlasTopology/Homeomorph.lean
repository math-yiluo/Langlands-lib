import Langlands.Geometry.Analytic.AtlasTopology.Definitions

/-! # Homeomorphism transport of atlas families -/

universe u v

namespace Langlands.Analytic.AtlasTopology

open Set Filter
open scoped Topology

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The family of actual images of the members under a homeomorphism. -/
def imageFamily (e : X ≃ₜ Y) (τ : Set (Set X)) : Set (Set Y) :=
  (fun U => e '' U) '' τ

theorem imageFamily_symm (e : X ≃ₜ Y) (τ : Set (Set X)) :
    imageFamily e.symm (imageFamily e τ) = τ := by
  ext U
  constructor
  · rintro ⟨_, ⟨V, hV, rfl⟩, rfl⟩
    have h : e.symm '' (e '' V) = V := e.toEquiv.symm_image_image V
    change e.symm '' (e '' V) ∈ τ
    rwa [h]
  · intro hU
    exact ⟨e '' U, ⟨U, hU, rfl⟩, e.toEquiv.symm_image_image U⟩

/-- Finite neighborhoods push forward to finite neighborhoods. -/
theorem IsQuasinet.imageFamily {τ : Set (Set X)} (hτ : IsQuasinet τ)
    (e : X ≃ₜ Y) : IsQuasinet (imageFamily e τ) := by
  intro y
  obtain ⟨σ, hfin, hsub, hmem, hnhds⟩ := hτ (e.symm y)
  refine ⟨(fun U => e '' U) '' σ, hfin.image _, ?_, ?_, ?_⟩
  · exact Set.image_mono hsub
  · rintro _ ⟨U, hU, rfl⟩
    exact ⟨e.symm y, hmem U hU, e.apply_symm_apply y⟩
  · have h := e.isOpenMap.image_mem_nhds hnhds
    rw [e.apply_symm_apply] at h
    apply Filter.mem_of_superset h
    rintro _ ⟨x, ⟨U, hU, hx⟩, rfl⟩
    exact ⟨e '' U, ⟨U, hU, rfl⟩, ⟨x, hx, rfl⟩⟩

/-- Restriction to a subspace commutes with image-family transport, using
the actual subspace homeomorphism rather than an ambient topology. -/
theorem imageFamily_restrictedFamily (e : X ≃ₜ Y) (τ : Set (Set X)) (S : Set X) :
    imageFamily (e.image S) (restrictedFamily τ S) =
      restrictedFamily (imageFamily e τ) (e '' S) := by
  ext W
  constructor
  · rintro ⟨_, ⟨U, hU, hUS, rfl⟩, rfl⟩
    refine ⟨e '' U, ⟨U, hU, rfl⟩, Set.image_mono hUS, ?_⟩
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, hx, rfl⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨⟨x, hUS hx⟩, hx, Subtype.ext hxy⟩
  · rintro ⟨_, ⟨U, hU, rfl⟩, hUS, rfl⟩
    have hUS' : U ⊆ S := by
      intro x hx
      obtain ⟨z, hz, hzx⟩ := hUS ⟨x, hx, rfl⟩
      exact e.injective hzx ▸ hz
    refine ⟨Subtype.val ⁻¹' U, ⟨U, hU, hUS', rfl⟩, ?_⟩
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, hx, rfl⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨⟨x, hUS' hx⟩, hx, Subtype.ext hxy⟩

/-- Transport of the quasinet on any contained-family subspace. -/
theorem IsQuasinet.imageFamily_restricted {τ : Set (Set X)} {S : Set X}
    (hτ : IsQuasinet (restrictedFamily τ S)) (e : X ≃ₜ Y) :
    IsQuasinet (restrictedFamily (AtlasTopology.imageFamily e τ) (e '' S)) := by
  rw [← imageFamily_restrictedFamily]
  exact hτ.imageFamily (e.image S)

theorem IsNet.imageFamily {τ : Set (Set X)} (hτ : IsNet τ) (e : X ≃ₜ Y) :
    IsNet (imageFamily e τ) := by
  refine ⟨hτ.1.imageFamily e, ?_⟩
  rintro _ ⟨U, hU, rfl⟩ _ ⟨V, hV, rfl⟩
  rw [← Set.image_inter e.injective]
  exact (hτ.2 U hU V hV).imageFamily_restricted e

theorem isQuasinet_imageFamily_iff (e : X ≃ₜ Y) (τ : Set (Set X)) :
    IsQuasinet (imageFamily e τ) ↔ IsQuasinet τ := by
  constructor
  · intro h
    simpa only [imageFamily_symm] using h.imageFamily e.symm
  · exact fun h => h.imageFamily e

theorem isNet_imageFamily_iff (e : X ≃ₜ Y) (τ : Set (Set X)) :
    IsNet (imageFamily e τ) ↔ IsNet τ := by
  constructor
  · intro h
    simpa only [imageFamily_symm] using h.imageFamily e.symm
  · exact fun h => h.imageFamily e

theorem IsCompactFamily.imageFamily {τ : Set (Set X)} (hτ : IsCompactFamily τ)
    (e : X ≃ₜ Y) : IsCompactFamily (imageFamily e τ) := by
  rintro _ ⟨U, hU, rfl⟩
  let : T2Space U := (hτ U hU).2
  exact ⟨(hτ U hU).1.image e.continuous, (e.image U).t2Space⟩

theorem isCompactFamily_imageFamily_iff (e : X ≃ₜ Y) (τ : Set (Set X)) :
    IsCompactFamily (imageFamily e τ) ↔ IsCompactFamily τ := by
  constructor
  · intro h
    simpa only [imageFamily_symm] using h.imageFamily e.symm
  · exact fun h => h.imageFamily e

end Langlands.Analytic.AtlasTopology
