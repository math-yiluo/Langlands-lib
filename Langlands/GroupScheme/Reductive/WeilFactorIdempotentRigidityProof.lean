import Langlands.GroupScheme.Reductive.WeilFactorRigidityReduction
import Langlands.GroupScheme.Reductive.RelativeAlmostSimpleNormalIdempotentProof
import Langlands.GroupScheme.Reductive.WeilAbelianImageTrivialityProof

/-! # Normal idempotents of a Weil restriction with almost simple geometric fibres -/

universe u

namespace Langlands.GroupScheme

/-- A conjugation-equivariant idempotent of the restricted Weil group functor
is the factor projection of a unique idempotent of the coefficient algebra. -/
theorem weilFactorIdempotentRigidity : WeilFactorIdempotentRigidityStatement.{u} :=
  WeilFactor.weilFactorIdempotentRigidity_of_inputs
    relativeAlmostSimpleNormalIdempotent weilAbelianImageTriviality

end Langlands.GroupScheme
