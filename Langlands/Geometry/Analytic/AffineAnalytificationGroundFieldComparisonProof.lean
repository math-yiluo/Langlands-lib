import Langlands.Geometry.Analytic.AffineAnalytificationChartBaseChangeProof
import Langlands.Geometry.Analytic.AffineGroundFieldComparison.Strong

/-! # The strong comparison of the two affine ground field extensions -/

universe u u' v

namespace Langlands.Analytic.AffineAnalytification

/-- The actual scalar-extended affine atlas and the affine atlas of the
algebraic base change are compared by a compatible strong quasi-isomorphism
over the original analytification, with the coordinate equations at every
admissible chart pair. -/
theorem affineAnalytificationGroundFieldComparison :
    AffineAnalytificationGroundFieldComparisonStatement.{u, u', v} :=
  GroundFieldComparison.reduceStrongComparison affineAnalytificationChartBaseChange

end Langlands.Analytic.AffineAnalytification
