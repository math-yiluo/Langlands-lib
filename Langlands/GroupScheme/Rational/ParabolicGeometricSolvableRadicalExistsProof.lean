import Langlands.GroupScheme.Rational.ParabolicGeometricSolvableRadicalReduction
import Langlands.GroupScheme.Rational.ReductiveGeometricSolvableRadicalReduction
import Langlands.GroupScheme.Rational.SolvableRadicalExistenceProof
import Langlands.GroupScheme.Rational.AlgClosedNormalSolvableTorusProof
import Langlands.GroupScheme.Rational.LargestCentralSubtorusBaseChangeProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # Geometric solvable radicals of rational parabolics: proof -/

universe u

namespace Langlands.GroupScheme

/-- Every rational parabolic of a connected reductive group over an arbitrary field has a
represented solvable radical that remains the solvable radical over the algebraic closure. -/
theorem parabolicGeometricSolvableRadicalExists :
    ParabolicGeometricSolvableRadicalExistsStatement.{u} :=
  parabolicGeometricSolvableRadicalExists_of_structure parabolicDynamic
    dynamicCentralizerReductive
    (reductiveGeometricSolvableRadicalExists_of_structure solvableRadicalExistence
      algClosedReductiveNormalSolvableTorus reductiveLargestCentralSubtorusBaseChange)

end Langlands.GroupScheme
