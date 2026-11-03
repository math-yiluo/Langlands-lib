import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityReduction
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Lie.SubgroupEqualityProof

/-! # Integral root annihilation implies actual centrality -/

universe u

namespace Langlands.GroupScheme

/-- A cocharacter annihilating every actual relative root has central image,
over every field and without a reductivity or maximality assumption. -/
theorem rootAnnihilatorCentrality : RootAnnihilatorCentralityStatement.{u} :=
  rootAnnihilatorCentrality_of_dynamic_geometry
    dynamicLie dynamicSmooth lieSubgroupEquality

end Langlands.GroupScheme
