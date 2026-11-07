import Langlands.GroupScheme.Reductive.GenericSpreadingFromLocus
import Langlands.GroupScheme.Reductive.IdentityComponentLocusProof

/-! # Generic reductivity on a nonempty principal open -/

universe u

namespace Langlands.GroupScheme

/-- A smooth affine group over a Noetherian domain with connected reductive
fraction-field fibre is connected reductive at every field-valued point of
one nonempty principal open. -/
theorem genericReductivitySpreading : GenericReductivitySpreadingStatement.{u} :=
  genericReductivitySpreading_of_identityComponentLocusOpen
    identityComponentReductiveLocusOpen

end Langlands.GroupScheme
