import Langlands.GroupScheme.Absolute.BorelCentralizerCenterReduction
import Langlands.GroupScheme.Absolute.BorelHomomorphismRigidityProof

/-! # Proof: the centralizer of a Borel subgroup is the centre -/

universe u

namespace Langlands.GroupScheme

/-- Milne, Proposition 17.22, as an equality of all-test subgroup functors. -/
theorem borelCentralizerCenter : BorelCentralizerCenterStatement.{u} :=
  borelCentralizerCenter_of_homomorphismRigidity borelHomomorphismRigidity

end Langlands.GroupScheme
