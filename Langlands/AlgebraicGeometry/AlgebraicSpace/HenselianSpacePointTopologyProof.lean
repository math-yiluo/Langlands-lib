import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianSpacePointTopologyStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopologyAdmissibleProof

/-!
# Proof of Conrad's Proposition 5.4 (corrected to locally separated spaces)

The étale-chart topology is the unique admissible family of topologies, so it witnesses
the existence statement.
-/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- **Conrad's Proposition 5.4** (corrected to locally separated spaces). -/
theorem henselianSpacePointTopology : HenselianSpacePointTopologyStatement.{u} :=
  fun K _ hK => ⟨etaleChartTopology K, (etaleChartTopologyAdmissible K hK).1,
    fun τ' hτ' X hX => (etaleChartTopologyAdmissible K hK).2.1 τ' hτ' X hX,
    (etaleChartTopologyAdmissible K hK).2.2⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
