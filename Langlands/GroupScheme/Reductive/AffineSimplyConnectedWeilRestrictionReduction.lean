import Langlands.GroupScheme.Reductive.AffineSimplyConnectedWeilRestrictionStatement
import Langlands.GroupScheme.Reductive.SimplyConnectedWeilExistenceReduction
import Langlands.GroupScheme.Reductive.AffineSplitIsomorphismTheoremProof
import Langlands.GroupScheme.Reductive.WeilFactorUniquenessReduction

/-! # The exact affine simply connected Weil target from pair descent and rigidity -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option linter.defProp false in
/-- The unchanged affine simply connected Weil-restriction target follows
from the two explicit shared structural inputs. The affine split isomorphism
input to existence is discharged by its published exact proof. -/
def affineSimplyConnectedWeilRestriction_of_pairDescent_and_rigidity
    (hD : AffineWeilPairEtaleDescentStatement.{u})
    (hR : WeilFactorIdempotentRigidityStatement.{u}) :
    AffineSimplyConnectedWeilRestrictionStatement.{u} := by
  intro A _ G hG hsc hnt
  exact ⟨(AffineSimplyConnectedWeilPresentation.ofReductive affineSplitIsomorphismTheorem
      hD G hG hsc hnt).exists_pair,
    WeilFactor.affineSimplyConnectedWeilRestriction_uniqueness_of_rigidity hR A G⟩

end Langlands.GroupScheme
