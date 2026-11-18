import Langlands.GroupScheme.Rational.GeometricBorelCentralizerCenterReduction
import Langlands.GroupScheme.Absolute.BorelCentralizerCenterReduction
import Langlands.GroupScheme.Absolute.BorelHomomorphismRigidityProof
import Langlands.GroupScheme.Absolute.BorelCenterEqualityReduction
import Langlands.GroupScheme.Absolute.BorelContainingSubgroupSelfNormalizerProof

/-! # Proof: the centralizer of a Borel subgroup over an arbitrary field -/

universe u

namespace Langlands.GroupScheme

/-- **Milne 17.70.** For a Borel subgroup `i : B ⟶ G`, in the geometric sense, of a smooth
connected affine group over any field, `Z(B) = C_G(B) = Z(G)`. -/
theorem geometricBorelCentralizerCenter : GeometricBorelCentralizerCenterStatement.{u} :=
  have hCentralizer : BorelCentralizerCenterStatement.{u} :=
    borelCentralizerCenter_of_homomorphismRigidity borelHomomorphismRigidity
  geometricBorelCentralizerCenterReduction hCentralizer
    (borelCenterEqualityReduction hCentralizer borelContainingSubgroupSelfNormalizer)

end Langlands.GroupScheme
