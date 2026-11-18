import Langlands.GroupScheme.Reductive.AdjointWeilFinalReduction
import Langlands.GroupScheme.Reductive.WeilChartSingleChartDescent
import Langlands.GroupScheme.Reductive.WeilFactorRigidityReduction
import Langlands.GroupScheme.Reductive.RelativeAlmostSimpleNormalIdempotentProof
import Langlands.GroupScheme.Reductive.WeilAbelianImageTrivialityProof
import Langlands.AlgebraicGeometry.FiniteEtaleChartDescentProof

/-! # The affine adjoint Weil restriction theorem -/

universe u
namespace Langlands.GroupScheme

/-- The original affine adjoint Weil restriction statement, with no extra hypotheses. -/
theorem affineAdjointWeilRestriction : AffineAdjointWeilRestrictionStatement.{u} := by
  have hR : WeilFactorIdempotentRigidityStatement.{u} :=
    WeilFactor.weilFactorIdempotentRigidity_of_inputs
      relativeAlmostSimpleNormalIdempotent weilAbelianImageTriviality
  exact affineAdjointWeilRestriction_of_descent_rigidity
    (affineWeilPairEtaleDescent hR Langlands.AlgebraicGeometry.finiteEtaleChartDescent) hR

end Langlands.GroupScheme
