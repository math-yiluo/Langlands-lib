import Langlands.GroupScheme.Reductive.RelativeDerivedGroupExistenceProof
import Langlands.GroupScheme.Reductive.RelativeSemisimpleFppfPerfectProof
import Langlands.GroupScheme.Reductive.RelativeDerivedReduction

/-! # The relative derived group of a reductive group scheme -/

noncomputable section
universe u

namespace Langlands.GroupScheme

/-- Every reductive group scheme has a unique relative derived subgroup,
with its fppf commutator, base-change and quotient universal properties. -/
theorem relativeDerivedGroup : RelativeDerivedGroupStatement.{u} :=
  relativeDerivedGroup_of_inputs relativeDerivedGroupExistence relativeSemisimpleFppfPerfect

end Langlands.GroupScheme
