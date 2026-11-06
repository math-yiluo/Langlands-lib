import Langlands.GroupScheme.Reductive.RankOneProjectiveBorelAssembly
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerFromQuotient
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof

/-! # Uniqueness of the positive root in semisimple rank one -/

noncomputable section

universe u

namespace Langlands.GroupScheme

/-- A cocharacter is positive on at most one actual root when every pair of
roots is integrally dependent. The projective Borel reduction and the
algebraically closed centralizer assembly have all their inputs supplied. -/
theorem rankOnePositiveRootUniqueness :
    RankOnePositiveRootUniquenessStatement.{u} :=
  rankOnePositiveRootUniqueness_of_projectiveBorelInputs
    (algClosedMaximalTorusCentralizer_fromQuotient
      dynamicCentralizerReductive solvableTorusQuotient)

end Langlands.GroupScheme
