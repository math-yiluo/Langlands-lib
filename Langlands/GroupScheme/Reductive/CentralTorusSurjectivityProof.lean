import Langlands.GroupScheme.Reductive.CentralTorusSurjectivityReduction
import Langlands.GroupScheme.Reductive.CentralTorusSemisimpleQuotientProof
import Langlands.GroupScheme.Derived.SemisimplePerfectProof

/-! # A central torus and the derived subgroup cover a connected reductive group -/

universe u

namespace Langlands.GroupScheme

/-- Over every field, some closed central torus of a connected reductive group multiplies
with any given derived-subgroup inclusion onto all points of the group. -/
theorem reductiveCentralTorusSurjectivity :
    ReductiveCentralTorusSurjectivityStatement.{u} :=
  reductiveCentralTorusSurjectivity_of_semisimpleQuotient.{u}
    reductiveCentralTorusSemisimpleQuotient.{u} semisimplePerfect.{u}

end Langlands.GroupScheme
