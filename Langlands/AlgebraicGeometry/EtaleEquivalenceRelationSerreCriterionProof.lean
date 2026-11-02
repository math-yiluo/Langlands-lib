import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationSerreReduction
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationRingFormProof
import Langlands.AlgebraicGeometry.GroupoidCoactionNonzeroInvariantProof

/-! # The Serre criterion for Noetherian affine étale equivalence relations -/

universe u

namespace Langlands.AlgebraicGeometry

/-- A Noetherian affine étale equivalence relation with an affine closed relation
and acyclic coactions has an affine quotient, with exactly the published hypotheses. -/
theorem etaleEquivalenceRelationSerreCriterion :
    EtaleEquivalenceRelationSerreCriterionStatement.{u} :=
  serreCriterion_of_ringForm_of_nonzeroInvariant
    etaleEquivalenceRelationRingForm groupoidCoactionNonzeroInvariant

end Langlands.AlgebraicGeometry
