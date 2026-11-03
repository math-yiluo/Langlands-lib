import Langlands.GroupScheme.Derived.CentralIntersectionReduction
import Langlands.GroupScheme.Derived.CentralIntersection.AlgClosed

/-! # Proof of finiteness of the full central intersection with an actual derived subgroup -/

universe u

namespace Langlands.GroupScheme

/-- The inverse image of the full scheme-theoretic centre under an actual derived-subgroup
inclusion of a connected reductive field group has a finite closed representative. -/
theorem derivedCentralIntersectionFiniteness : DerivedCentralIntersectionFinitenessStatement.{u} :=
  derivedCentralIntersectionFiniteness_of_algClosed CentralIntersection.finite_of_isAlgClosed

end Langlands.GroupScheme
