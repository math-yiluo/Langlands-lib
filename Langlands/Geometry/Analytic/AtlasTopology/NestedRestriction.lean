import Langlands.Geometry.Analytic.AtlasTopology.Restriction

/-! # Nested subspace restriction of quasinet families -/

universe u

namespace Langlands.Analytic.AtlasTopology

open Set

variable {X : Type u} [TopologicalSpace X]

/-- A contained ambient subset and its copy in the induced subspace have
their actual induced topologies. -/
def nestedRestrictionHomeomorph (S T : Set X) (hTS : T ⊆ S) :
    T ≃ₜ (Subtype.val ⁻¹' T : Set S) where
  toFun x := ⟨⟨x.val, hTS x.property⟩, x.property⟩
  invFun y := ⟨y.val.val, y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- Restriction first to a larger subspace and then to a contained subset
keeps exactly the same original members. -/
theorem nestedRestrictionHomeomorph_imageFamily (τ : Set (Set X))
    (S T : Set X) (hTS : T ⊆ S) :
    imageFamily (nestedRestrictionHomeomorph S T hTS) (restrictedFamily τ T) =
      restrictedFamily (restrictedFamily τ S) (Subtype.val ⁻¹' T) := by
  ext W
  constructor
  · rintro ⟨_, ⟨V, hV, hVT, rfl⟩, rfl⟩
    have hVS : V ⊆ S := hVT.trans hTS
    refine ⟨Subtype.val ⁻¹' V, ⟨V, hV, hVS, rfl⟩, ?_, ?_⟩
    · intro x hx
      exact hVT hx
    · ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        exact ⟨⟨y.val.val, y.property⟩, hy, Subtype.ext (Subtype.ext rfl)⟩
  · rintro ⟨_, ⟨V, hV, hVS, rfl⟩, hVT, rfl⟩
    have hVT' : V ⊆ T := fun x hx =>
      hVT (show (⟨x, hVS hx⟩ : S) ∈ (Subtype.val ⁻¹' V : Set S) from hx)
    refine ⟨Subtype.val ⁻¹' V, ⟨V, hV, hVT', rfl⟩, ?_⟩
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y.val.val, y.property⟩, hy, Subtype.ext (Subtype.ext rfl)⟩

/-- The quasinet condition is independent of whether a contained subset
is regarded directly in the ambient space or in the intermediate subspace. -/
theorem isQuasinet_nested_restrictedFamily_iff (τ : Set (Set X))
    (S T : Set X) (hTS : T ⊆ S) :
    IsQuasinet (restrictedFamily (restrictedFamily τ S) (Subtype.val ⁻¹' T)) ↔
      IsQuasinet (restrictedFamily τ T) := by
  rw [← nestedRestrictionHomeomorph_imageFamily τ S T hTS]
  exact isQuasinet_imageFamily_iff _ _

/-- The image of an arbitrary subset of a subtype gives the ambient
version of the same contained-member quasinet. -/
theorem isQuasinet_restrictedFamily_subtype_iff (τ : Set (Set X))
    (S : Set X) (U : Set S) :
    IsQuasinet (restrictedFamily (restrictedFamily τ S) U) ↔
      IsQuasinet (restrictedFamily τ (Subtype.val '' U)) := by
  have h := isQuasinet_nested_restrictedFamily_iff τ S (Subtype.val '' U)
    (by rintro x ⟨y, _, rfl⟩; exact y.property)
  rwa [Set.preimage_image_eq U Subtype.val_injective] at h

omit [TopologicalSpace X] in
/-- Taking ambient images and restricting back to the subtype recovers
an arbitrary family of subsets exactly. -/
theorem restrictedFamily_subtype_images (S : Set X) (τ : Set (Set S)) :
    restrictedFamily ((fun V : Set S => Subtype.val '' V) '' τ) S = τ := by
  ext W
  constructor
  · rintro ⟨_, ⟨V, hV, rfl⟩, _, rfl⟩
    simpa only [Set.preimage_image_eq V Subtype.val_injective] using hV
  · intro hW
    refine ⟨Subtype.val '' W, ⟨W, hW, rfl⟩, ?_, ?_⟩
    · rintro x ⟨y, _, rfl⟩
      exact y.property
    · exact (Set.preimage_image_eq W Subtype.val_injective).symm

/-- Arbitrary families on a subspace and their ambient images give the
same quasinet covering condition on corresponding target subsets. -/
theorem isQuasinet_restrictedFamily_subtype_images_iff (S : Set X)
    (τ : Set (Set S)) (U : Set S) :
    IsQuasinet (restrictedFamily τ U) ↔
      IsQuasinet (restrictedFamily ((fun V : Set S => Subtype.val '' V) '' τ)
        (Subtype.val '' U)) := by
  have h := isQuasinet_restrictedFamily_subtype_iff
    ((fun V : Set S => Subtype.val '' V) '' τ) S U
  rwa [restrictedFamily_subtype_images] at h

end Langlands.Analytic.AtlasTopology
