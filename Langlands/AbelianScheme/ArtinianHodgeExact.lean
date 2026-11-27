import Langlands.AbelianScheme.ArtinianHodgeClosedForms
import Langlands.AbelianScheme.ArtinianHodgeSurjectivity

/-! # The finite free degree-one Hodge sequence for Artinian abelian schemes -/

universe u

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.AffineCechDeRham

/-- The degree-one Hodge sequence on any supplied finite affine cover has
injective first arrow, surjective second arrow and finite free end modules. -/
theorem artinianHodgeExact : ArtinianHodgeExactStatement.{u} := by
  intro R _ _ _ _ B U _
  obtain ⟨hcFinite, hcFree⟩ := closedForms_finite_free B U
  exact ⟨closedFormClass_injective B U, toStructureH1_surjective_artinian B U,
    hcFinite, hcFree, structureH1_finite B.X.hom U, structureH1_free_artinian B U⟩

end Langlands.AbelianScheme
