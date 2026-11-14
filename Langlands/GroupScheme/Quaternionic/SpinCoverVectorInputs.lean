import Langlands.GroupScheme.Quaternionic.SpinCoverVectorReduction

/-! # The two remaining representation inputs for aligned spin vector weights -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Module
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.GroupScheme

/-- The two representation existence results used by the aligned spin-vector
weight reduction. Neither conjunct is included as an axiom. -/
def SpinCoverVectorRepresentationInputs : Prop :=
  Quaternionic.OrthogonalMoritaRepresentationStatement.{u} ∧
    OrthogonalMatrix.NumberedCoverVectorStatement.{u}

/-- The host statement follows from the two explicitly retained representation
inputs, choosing the comparison over the algebraic closure of the separable
closure and descending its characters by the supplied-comparison reduction. -/
theorem spinCoverVectorWeights_of_representation_inputs
    (hMorita : Quaternionic.OrthogonalMoritaRepresentationStatement.{u})
    (hNumbered : OrthogonalMatrix.NumberedCoverVectorStatement.{u}) :
    SpinCoverVectorWeightsStatement.{u} := by
  classical
  intro K _ G _ _ d n e hn _hsc _haas hcartan D _ _ _ _ degree m
    hdegree hdim hmn sigma horth q hq pi hpi halign
  let L := AlgebraicClosure (SeparableClosure K)
  obtain ⟨mor⟩ := hMorita K D degree m n hdegree hn hdim hmn sigma horth q hq L
  exact spinCoverVectorWeights_of_comparison d e hn mor hpi hNumbered
    hdegree hdim hcartan halign

/-- The packaged pair of representation inputs suffices for the host theorem. -/
theorem SpinCoverVectorRepresentationInputs.vectorWeights
    (h : SpinCoverVectorRepresentationInputs.{u}) :
    SpinCoverVectorWeightsStatement.{u} :=
  spinCoverVectorWeights_of_representation_inputs h.1 h.2

end Langlands.GroupScheme
