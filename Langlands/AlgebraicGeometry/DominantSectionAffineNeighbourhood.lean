import Langlands.AlgebraicGeometry.GenericPointAvoidance
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Affine neighbourhoods from dominant sections -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- A dominant section over an open of a separated morphism with reduced
source is an open immersion. -/
theorem isOpenImmersion_of_dominant_section
    {S Z : Scheme.{u}} [IsReduced Z]
    (f : Z ⟶ S) [IsSeparated f]
    (U : S.Opens) (s : U.toScheme ⟶ Z) [IsDominant s]
    (hs : s ≫ f = U.ι) : IsOpenImmersion s := by
  let W := f ⁻¹ᵁ U
  have hr : Set.range s ⊆ Set.range W.ι := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨s x, ?_⟩, rfl⟩
    change f (s x) ∈ U
    change (s ≫ f) x ∈ U
    rw [hs]
    exact x.2
  let t := IsOpenImmersion.lift W.ι s hr
  have ht : t ≫ W.ι = s := IsOpenImmersion.lift_fac _ _ _
  have hq : t ≫ (f ∣_ U) = 𝟙 U.toScheme := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, ht, hs,
      Category.id_comp]
  have : IsClosedImmersion (t ≫ (f ∣_ U)) := by rw [hq]; infer_instance
  have : IsClosedImmersion t := IsClosedImmersion.of_comp t (f ∣_ U)
  have : IsDominant (t ≫ W.ι) := by rw [ht]; infer_instance
  have : IsDominant t := IsDominant.of_comp_of_isOpenImmersion t W.ι
  have : Surjective t := surjective_of_isDominant_of_isClosed_range t
    t.isClosedEmbedding.isClosed_range
  have : IsIso t := isIso_of_isClosedImmersion_of_surjective t
  rw [← ht]
  infer_instance

/-- A finite set in the domain of a dominant section into a reduced affine
scheme has an affine neighbourhood in the original scheme. -/
def affineNeighbourhoodOfDominantSection
    {S Z : Scheme.{u}} [IsReduced Z] [IsAffine Z]
    (f : Z ⟶ S) [IsSeparated f]
    (U : S.Opens) (s : U.toScheme ⟶ Z) [IsDominant s]
    (hs : s ≫ f = U.ι) (E : Set S) (hE : E.Finite) (hEU : E ⊆ U) :
    {V : S.Opens // IsAffineOpen V ∧ E ⊆ V} := by
  apply Classical.choice
  have : IsOpenImmersion s := isOpenImmersion_of_dominant_section f U s hs
  have hF : (U.ι ⁻¹' E).Finite :=
    hE.preimage U.ι.isOpenEmbedding.injective.injOn
  obtain ⟨a, haE, haU⟩ := GenericPointAvoidance.exists_basicOpen_of_finite
    (hF.image s) (W := s.opensRange) (Set.image_subset_range _ _)
  let W := s ⁻¹ᵁ Z.basicOpen a
  have hW : IsAffineOpen W :=
    ((isAffineOpen_top Z).basicOpen a).preimage_of_isOpenImmersion s haU
  refine ⟨⟨U.ι ''ᵁ W, hW.image_of_isOpenImmersion U.ι, ?_⟩⟩
  intro x hx
  exact ⟨⟨x, hEU hx⟩, haE ⟨⟨x, hEU hx⟩, hx, rfl⟩, rfl⟩

end Langlands.AlgebraicGeometry
