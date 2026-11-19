import Langlands.GroupScheme.QuasiFiniteCommutativeUniformExponentProof
import Langlands.GroupScheme.Torus.FiniteSubgroupSpreadingReduction

/-! # Spreading of finite and trivial fibres of closed subgroups -/

universe u

namespace Langlands.GroupScheme

/-- A finite fibre of a closed subgroup spreads to a finite neighbourhood with a
uniform exponent, and a unit fibre spreads to a trivial neighbourhood
(SGA 3, Exposé IX, Theorem 6.4 and Corollary 6.5). -/
theorem multiplicativeTypeFiniteSubgroupSpreading :
    MultiplicativeTypeFiniteSubgroupSpreadingStatement.{u} :=
  FiniteSubgroupSpreadingReduction.finiteSubgroupSpreading_of_uniformExponent
    quasiFiniteCommutativeUniformExponent

end Langlands.GroupScheme
