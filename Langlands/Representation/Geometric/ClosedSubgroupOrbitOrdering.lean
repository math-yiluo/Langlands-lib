import Langlands.Representation.Geometric.CosetOrbitOrdering
import Langlands.Topology.GroupAction.FiniteOrbitProof

/-! Finite closed-subgroup double cosets admit an ordering with open initial unions. -/

namespace Langlands.Geometric

universe uG

/-- The finite double-coset orbit ordering, with the original closed-subgroup
hypotheses and the convention `P w⁻¹ Q`. -/
theorem closedSubgroupOrbitOrdering : ClosedSubgroupOrbitOrdering.{uG} :=
  closedSubgroupOrbitOrdering_of_finiteOrbitOrdering
    Langlands.Topology.finiteOrbitOrdering.{uG, uG}

end Langlands.Geometric
