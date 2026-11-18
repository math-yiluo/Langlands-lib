import Langlands.GroupScheme.Reductive.FpqcLocalIsomorphismReduction
import Langlands.GroupScheme.Reductive.AffineSplitIsomorphismTheoremProof

/-! # Fpqc-locally isomorphic reductive groups are étale-locally isomorphic -/

universe u

namespace Langlands.GroupScheme

/-- The unchanged fpqc-to-étale local-isomorphism statement over every base. -/
theorem reductiveFpqcLocalIsomorphism :
    ReductiveFpqcLocalIsomorphismStatement.{u} :=
  reductiveFpqcLocalIsomorphism_of_affineSplit.{u} affineSplitIsomorphismTheorem.{u}

end Langlands.GroupScheme
