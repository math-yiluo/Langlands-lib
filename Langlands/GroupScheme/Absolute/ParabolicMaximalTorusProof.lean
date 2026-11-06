import Langlands.GroupScheme.Absolute.ParabolicMaximalTorusReduction
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Absolute.BorelMaximalTorusProof
import Langlands.GroupScheme.Absolute.BorelContainingSubgroupConnected
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.GeometricConnectedness

/-! # A parabolic subgroup contains a maximal torus of the ambient group -/

universe u

namespace Langlands.GroupScheme

/-- A parabolic subgroup contains a torus over the original field that is maximal in the
ambient connected reductive group. -/
theorem parabolicMaximalTorus : ParabolicMaximalTorusStatement.{u} := by
  apply parabolicMaximalTorus_of_structuralInputs
  refine ⟨maximalTorusExistence, maximalTorusBaseChange, borelMaximalTorus,
    borelContainingSubgroupConnectedStatement, ?_, ?_⟩
  · intro k _ _ G _ _ _ T T' j j' hj hj'
    exact (subgroupConjugate_iff_exists_commGroupSchemeIso j j').mpr
      (maximalTorusConjugacy k G T T' j j' hj hj')
  · intro k _ G hG
    exact hG.connectedSpace_toAlgebraicClosure

end Langlands.GroupScheme
