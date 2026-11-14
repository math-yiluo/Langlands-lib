import Langlands.GroupScheme.SimplyConnected.OuterTypeARankOneHermitianReduction
import Langlands.GroupScheme.SimplyConnected.OuterTypeAHermitianPresentationProof
import Langlands.GroupScheme.Rational.HermitianMatrixSplitRankProof

/-! # Hermitian models for rank-one outer type-A indices -/

universe u

namespace Langlands.GroupScheme

/-- The actual rank-one outer-A index gives a special unitary Hermitian model
with anisotropic middle over a separable quadratic extension. -/
theorem outerTypeARankOneHermitian : OuterTypeARankOneHermitianStatement.{u} :=
  outerTypeARankOneHermitian_of_presentation_and_splitRank
    outerTypeAHermitianPresentation hermitianMatrixSplitRank

end Langlands.GroupScheme
