import Langlands.GroupScheme.Rational.AlgClosedNormalSolvableTorusReduction
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof

/-! # Normal solvable subgroups of reductive groups are central tori -/

universe u

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, every smooth connected solvable normal
closed subgroup of a pseudo-reductive group is a central torus. -/
theorem algClosedReductiveNormalSolvableTorus :
    AlgClosedReductiveNormalSolvableTorusStatement.{u} :=
  algClosedReductiveNormalSolvableTorus_of_quotient.{u} solvableTorusQuotient.{u}

end Langlands.GroupScheme
