import Langlands.GroupScheme.Rational.ParabolicRadicalTorusInitialLevi
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # An initial radical torus with a rational Levi as its ambient centralizer -/

universe u

namespace Langlands.GroupScheme

/-- Each supplied geometric solvable radical of a parabolic has a maximal torus
whose ambient centralizer is represented by an actual rational Levi. -/
theorem parabolicRadicalTorusInitialCentralizerLevi :
    ParabolicRadicalTorusInitialCentralizerLeviStatement.{u} :=
  parabolicRadicalTorusInitialLevi_of_dynamic parabolicDynamic dynamicCentralizerReductive

end Langlands.GroupScheme
