import Langlands.GroupScheme.Absolute.BorelProperQuotientReduction
import Langlands.GroupScheme.Absolute.GeneralLinearSolvableStabilizerProof
import Langlands.GroupScheme.ClosedOrbitProof
import Langlands.GroupScheme.SolvableProperFixedPointProof

/-! # Some Borel subgroup has proper homogeneous quotients -/

universe u

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, some Borel subgroup of every connected smooth affine
group has proper actual homogeneous quotients. -/
theorem someBorelQuotientProper : SomeBorelQuotientProperStatement.{u} :=
  someBorelQuotientProper_of_prerequisites generalLinearSolvableStabilizer closedOrbit
    solvableProperFixedPoint

end Langlands.GroupScheme
