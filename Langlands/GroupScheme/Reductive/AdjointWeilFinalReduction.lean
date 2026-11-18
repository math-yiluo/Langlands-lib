import Langlands.GroupScheme.Reductive.AdjointWeilExistenceReduction
import Langlands.GroupScheme.Reductive.AffineAdjointWeilRestrictionReduction
import Langlands.GroupScheme.Reductive.AffineSplitIsomorphismTheoremProof

/-! # The affine adjoint Weil theorem from pair descent and factor rigidity -/

noncomputable section
universe u
namespace Langlands.GroupScheme

set_option linter.defProp false in
/-- The unchanged target follows from generic pair descent and factor rigidity.
The local presentation input is constructed using the proved affine split theorem. -/
def affineAdjointWeilRestriction_of_descent_rigidity
    (hD : AffineWeilPairEtaleDescentStatement.{u})
    (hR : WeilFactorIdempotentRigidityStatement.{u}) :
    AffineAdjointWeilRestrictionStatement.{u} :=
  affineAdjointWeilRestriction_of_inputs
    (fun M hnt => ⟨AffineAdjointWeilPresentation.ofPinnedModel
      affineSplitIsomorphismTheorem hD M hnt⟩) hD hR

end Langlands.GroupScheme
