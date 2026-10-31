import Langlands.Geometry.Analytic.AtlasTopology.Homeomorph
import Langlands.Geometry.Analytic.AtlasTopology.QuasinetProperties

/-! # Restriction of atlas nets to their members -/

universe u

namespace Langlands.Analytic.AtlasTopology

open Set Filter
open scoped Topology

variable {X : Type u} [TopologicalSpace X]

/-- The actual subspace identification of an intersection inside a larger subspace. -/
def restrictionInterHomeomorph (S U V : Set X) (hUS : U ⊆ S) :
    ↥(U ∩ V) ≃ₜ ↥((Subtype.val ⁻¹' U : Set S) ∩ Subtype.val ⁻¹' V) where
  toFun x := ⟨⟨x.val, hUS x.property.1⟩, x.property⟩
  invFun y := ⟨y.val.val, y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- Nested contained-member families agree through the actual subspace homeomorphism. -/
theorem restrictionInterHomeomorph_imageFamily (τ : Set (Set X))
    (S U V : Set X) (hUS : U ⊆ S) :
    imageFamily (restrictionInterHomeomorph S U V hUS) (restrictedFamily τ (U ∩ V)) =
      restrictedFamily (restrictedFamily τ S)
        ((Subtype.val ⁻¹' U : Set S) ∩ Subtype.val ⁻¹' V) := by
  ext T
  constructor
  · rintro ⟨_, ⟨W, hW, hWUV, rfl⟩, rfl⟩
    have hWS : W ⊆ S := fun _ hx => hUS (hWUV hx).1
    refine ⟨Subtype.val ⁻¹' W, ⟨W, hW, hWS, rfl⟩, ?_, ?_⟩
    · intro x hx
      exact hWUV hx
    · ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        refine ⟨⟨y.val.val, y.property⟩, hy, ?_⟩
        exact Subtype.ext (Subtype.ext rfl)
  · rintro ⟨_, ⟨W, hW, hWS, rfl⟩, hWUV, rfl⟩
    have hWUV' : W ⊆ U ∩ V := fun x hx => hWUV (show (⟨x, hWS hx⟩ : S) ∈
      (Subtype.val ⁻¹' W : Set S) from hx)
    refine ⟨Subtype.val ⁻¹' W, ⟨W, hW, hWUV', rfl⟩, ?_⟩
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y.val.val, y.property⟩, hy, Subtype.ext (Subtype.ext rfl)⟩

/-- A contained-member quasinet inherits the pairwise intersection axiom of a net. -/
theorem IsNet.restrict {τ : Set (Set X)} (hτ : IsNet τ) (S : Set X)
    (hS : IsQuasinet (restrictedFamily τ S)) : IsNet (restrictedFamily τ S) := by
  refine ⟨hS, ?_⟩
  rintro _ ⟨U, hU, hUS, rfl⟩ _ ⟨V, hV, _, rfl⟩
  have h := (hτ.2 U hU V hV).imageFamily (restrictionInterHomeomorph S U V hUS)
  rwa [restrictionInterHomeomorph_imageFamily] at h

/-- Restriction to a member is always a net: that member supplies the whole subspace. -/
theorem IsNet.restrict_member {τ : Set (Set X)} (hτ : IsNet τ)
    {S : Set X} (hS : S ∈ τ) : IsNet (restrictedFamily τ S) := by
  apply hτ.restrict S
  apply isQuasinet_of_univ_mem
  refine ⟨S, hS, Subset.rfl, ?_⟩
  ext x
  exact ⟨fun _ => x.property, fun _ => Set.mem_univ _⟩

end Langlands.Analytic.AtlasTopology
