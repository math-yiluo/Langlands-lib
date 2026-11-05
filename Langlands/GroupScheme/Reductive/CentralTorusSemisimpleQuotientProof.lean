import Langlands.GroupScheme.Reductive.CentralTorusSemisimpleQuotientReduction
import Langlands.GroupScheme.Rational.SolvableRadicalExistenceProof
import Langlands.GroupScheme.Rational.AlgClosedNormalSolvableTorusProof
import Langlands.GroupScheme.Rational.LargestCentralSubtorusBaseChangeProof

/-! # A central torus with semisimple quotient in every connected reductive group -/

universe u

namespace Langlands.GroupScheme

/-- Every connected reductive field group has an actual closed central torus
such that every affine fppf quotient by it is semisimple. -/
theorem reductiveCentralTorusSemisimpleQuotient :
    ReductiveCentralTorusSemisimpleQuotientStatement.{u} :=
  reductiveCentralTorusSemisimpleQuotient_of_structure.{u}
    solvableRadicalExistence.{u}
    algClosedReductiveNormalSolvableTorus.{u}
    reductiveLargestCentralSubtorusBaseChange.{u}

end Langlands.GroupScheme
