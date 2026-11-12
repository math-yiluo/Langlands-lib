import Langlands.GroupScheme.Derived.SuppliedCocenterTorusReduction
import Langlands.GroupScheme.Derived.CocenterQuotientProof

/-! # suppliedCocenterTorus: unconditional proof from published reductions -/

universe u

namespace Langlands.GroupScheme

/-- Every supplied commutative fppf quotient by an actual derived subgroup of a connected reductive field group is a torus. -/
theorem suppliedCocenterTorus :
    SuppliedCocenterTorusStatement.{u} :=
  suppliedCocenterTorus_of_existence cocenterQuotientExistence

end Langlands.GroupScheme
