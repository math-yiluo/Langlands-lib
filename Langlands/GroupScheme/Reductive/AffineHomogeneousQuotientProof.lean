import Langlands.GroupScheme.Reductive.AffineHomogeneousQuotientGeometricReductivity
import Langlands.GroupScheme.Reductive.GeometricReductivityProof

/-! # Reductivity from an affine homogeneous quotient -/

universe u

namespace Langlands.GroupScheme

/-- **Borel–Richardson criterion** (Conrad–Gabber–Prasad, proof of Proposition A.8.12). A smooth
closed subgroup of a connected reductive group over a field has connected reductive identity
component whenever its actual homogeneous quotient is affine. -/
theorem affineHomogeneousQuotientReductive : AffineHomogeneousQuotientReductiveStatement.{u} :=
  affineHomogeneousQuotientReductive_of_geometricReductivity reductiveGeometricReductivity

end Langlands.GroupScheme
