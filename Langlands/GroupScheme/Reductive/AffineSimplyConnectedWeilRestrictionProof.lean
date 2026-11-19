import Langlands.GroupScheme.Reductive.AffineSimplyConnectedWeilRestrictionReduction
import Langlands.GroupScheme.Reductive.WeilChartSingleChartDescent
import Langlands.GroupScheme.Reductive.WeilFactorRigidityReduction
import Langlands.GroupScheme.Reductive.RelativeAlmostSimpleNormalIdempotentProof
import Langlands.GroupScheme.Reductive.WeilAbelianImageTrivialityProof
import Langlands.AlgebraicGeometry.FiniteEtaleChartDescentProof

/-! # The affine simply connected Weil restriction theorem -/

universe u

namespace Langlands.GroupScheme

/-- The original affine simply connected Weil restriction statement, with no extra
hypotheses. -/
theorem affineSimplyConnectedWeilRestriction :
    AffineSimplyConnectedWeilRestrictionStatement.{u} := by
  have hR : WeilFactorIdempotentRigidityStatement.{u} :=
    WeilFactor.weilFactorIdempotentRigidity_of_inputs
      relativeAlmostSimpleNormalIdempotent weilAbelianImageTriviality
  exact affineSimplyConnectedWeilRestriction_of_pairDescent_and_rigidity
    (affineWeilPairEtaleDescent hR Langlands.AlgebraicGeometry.finiteEtaleChartDescent) hR

end Langlands.GroupScheme
