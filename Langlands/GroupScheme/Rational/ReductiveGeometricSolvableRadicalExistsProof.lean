import Langlands.GroupScheme.Rational.ReductiveGeometricSolvableRadicalReduction
import Langlands.GroupScheme.Rational.SolvableRadicalExistenceProof
import Langlands.GroupScheme.Rational.AlgClosedNormalSolvableTorusProof
import Langlands.GroupScheme.Rational.LargestCentralSubtorusBaseChangeProof

/-! # reductiveGeometricSolvableRadicalExists: unconditional proof from published reductions -/

universe u

namespace Langlands.GroupScheme

/-- Every connected reductive field group admits an actual represented solvable radical that remains a solvable radical after base change to the algebraic closure. -/
theorem reductiveGeometricSolvableRadicalExists :
    ReductiveGeometricSolvableRadicalExistsStatement.{u} :=
  reductiveGeometricSolvableRadicalExists_of_structure solvableRadicalExistence
    algClosedReductiveNormalSolvableTorus reductiveLargestCentralSubtorusBaseChange

end Langlands.GroupScheme
