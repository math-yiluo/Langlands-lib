import Langlands.GroupScheme.Reductive.RelativeDerivedGroupExistenceConstruction
import Langlands.GroupScheme.Reductive.RelativeSemisimpleFppfPerfectProof

/-! # Existence of the relative derived subgroup with torus quotient -/

noncomputable section
universe u

namespace Langlands.GroupScheme

/-- Every reductive group scheme has a closed normal relative semisimple
  subgroup whose represented fppf quotient is a relative torus. -/
theorem relativeDerivedGroupExistence : RelativeDerivedGroupExistenceStatement.{u} :=
  relativeDerivedGroupExistence_of_relativeSemisimpleFppfPerfect
    relativeSemisimpleFppfPerfect

end Langlands.GroupScheme
