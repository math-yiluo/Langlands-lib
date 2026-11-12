import Langlands.GroupScheme.Rational.ParabolicRadicalTorusInitialLevi
import Langlands.GroupScheme.Rational.SolvableMaximalTorusConjugacyProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # The centralizer Levi of a maximal torus of a parabolic radical -/

universe u

namespace Langlands.GroupScheme

/-- Over every field, the ambient whole-torus centralizer of any maximal torus
of a supplied geometric solvable radical of a rational parabolic is
represented by an actual rational Levi of that parabolic. -/
theorem parabolicRadicalTorusCentralizerLevi :
    ParabolicRadicalTorusCentralizerLeviStatement.{u} :=
  parabolicRadicalTorusCentralizerLevi_of_dynamic parabolicDynamic
    dynamicCentralizerReductive solvableMaximalTorusConjugacy

end Langlands.GroupScheme
