import Langlands.AlgebraicGeometry.Picard.ProperLineBundleIsomOfHom
import Langlands.AlgebraicGeometry.Picard.ProperLineBundleHomRepresentability

/-! # Affine scheme representation of actual line-bundle Isom -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- For a proper flat locally finitely presented morphism, the full-slice Isom
presheaf of two actual line-bundle families has an affine locally finitely
presented scheme representative. -/
theorem properLineBundleIsomRepresentability :
    ProperLineBundleIsomRepresentabilityStatement.{u} :=
  properLineBundleIsomRepresentability_of_hom properLineBundleHomRepresentability

end Langlands.AlgebraicGeometry.Picard
