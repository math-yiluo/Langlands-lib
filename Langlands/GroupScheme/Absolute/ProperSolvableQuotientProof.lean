import Langlands.GroupScheme.Absolute.ProperSolvableQuotient
import Langlands.GroupScheme.SolvableProperFixedPointProof

/-! # Proof of the proper solvable homogeneous quotient criterion -/

universe u

namespace Langlands.GroupScheme

/-- A smooth connected solvable closed subgroup with a proper actual homogeneous
quotient is Borel (Milne 2017, Proposition 17.19, (b) ⇒ (a)). -/
theorem properSolvableQuotientBorel : ProperSolvableQuotientBorelStatement.{u} :=
  properSolvableQuotientBorel_of_solvableProperFixedPoint solvableProperFixedPoint

end Langlands.GroupScheme
