import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Reductive.CenterMultiplicativeTypeReduction
import Langlands.GroupScheme.NormalQuotientExistenceProof
import Langlands.GroupScheme.AffineNormalSubgroupQuotientEquivalence
import Langlands.GroupScheme.Rational.MultiplicativeTypeSplitQuotientAnisotropyProof
import Langlands.GroupScheme.Rational.CenterSplitComponentCompactnessAlgebraicReduction

/-! # Compactness of the full scheme-center point quotient by a split component -/

universe u

namespace Langlands.GroupScheme

/-- The full scheme-center rational-point quotient by the actual image of any
split component is compact in its canonical inherited quotient topology. -/
theorem centerSplitComponentCompactness : CenterSplitComponentCompactnessStatement.{u} :=
  centerSplitComponentCompactnessAlgebraicReduction
    (centerMultiplicativeTypeCentralizerReduction
      (fun k _ _ G hG T j hj => maximalTorusCentralizer k G hG T j hj))
    normalSubgroupQuotientExistence.toAffineNormalSubgroupQuotientStatement
    multiplicativeTypeSplitQuotientAnisotropy

end Langlands.GroupScheme
