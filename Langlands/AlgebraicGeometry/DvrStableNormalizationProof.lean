import Langlands.AlgebraicGeometry.DvrStableNormalizationStatement
import Langlands.AlgebraicGeometry.DvrStableNormalization.Reduction
import Langlands.AlgebraicGeometry.DvrAffineReducedFibreProof

/-! # Proof of stable normal models over a discrete valuation ring -/

universe u

namespace Langlands.AlgebraicGeometry

/-- Proof of `DvrStableNormalizationStatement`: the reduction
`DvrStableNormalization.dvrStableNormalization_of_affineReducedFibre` applied to the proof of the
affine reduced fibre theorem. -/
theorem dvrStableNormalization : DvrStableNormalizationStatement.{u} :=
  DvrStableNormalization.dvrStableNormalization_of_affineReducedFibre dvrAffineReducedFibre

end Langlands.AlgebraicGeometry
