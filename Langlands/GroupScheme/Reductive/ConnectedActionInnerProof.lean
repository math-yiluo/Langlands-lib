import Langlands.GroupScheme.Reductive.ConnectedActionInnerReduction
import Langlands.GroupScheme.Reductive.InnerActionLocusProof

/-! # Actions with connected fibres on reductive group schemes are inner -/

universe u

namespace Langlands.GroupScheme

/-- An action by a group scheme with connected residue fibres on a reductive group
scheme factors uniquely through the supplied adjoint action. -/
theorem reductiveConnectedActionInner : ReductiveConnectedActionInnerStatement.{u} :=
  reductiveConnectedActionInner_of_innerActionLocus reductiveInnerActionLocus

end Langlands.GroupScheme
