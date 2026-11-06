import Langlands.GroupScheme.Absolute.BorelContainingSubgroupConnectedReduction
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Absolute.BorelNormalizerProof

/-! # Connectedness of smooth closed subgroups containing a Borel subgroup -/

universe u

namespace Langlands.GroupScheme

/-- A smooth closed subgroup containing a Borel subgroup of a smooth connected affine group
over an algebraically closed field is connected (Milne 17.49, connectedness clause). -/
theorem borelContainingSubgroupConnectedStatement :
    BorelContainingSubgroupConnectedStatement.{u} :=
  BorelContainingSubgroupConnected.borelContainingSubgroupConnected_of borelConjugacy
    borelNormalizer

end Langlands.GroupScheme
