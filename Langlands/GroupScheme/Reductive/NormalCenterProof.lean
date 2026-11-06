import Langlands.GroupScheme.Reductive.NormalCenterCentralizerReduction
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerFromQuotient
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof

/-! # Full centres of normal connected reductive subgroups -/

universe u

namespace Langlands.GroupScheme

/-- The full scheme-theoretic centre of a closed normal connected reductive
subgroup maps into the ambient full centre over every field. -/
theorem normalReductiveCenter : NormalReductiveCenterStatement.{u} :=
  normalReductiveCenterCentralizerReduction
    (algClosedMaximalTorusCentralizer_fromQuotient
      dynamicCentralizerReductive solvableTorusQuotient)

end Langlands.GroupScheme
