import Langlands.GroupScheme.Reductive.AffineAdjointWeilRestrictionStatement
import Langlands.GroupScheme.Reductive.AdjointWeilDescentReduction
import Langlands.GroupScheme.Reductive.WeilFactorUniquenessReduction

/-! # The exact affine adjoint Weil target reduced to three structural inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option linter.defProp false in
/-- Actual affine adjoint Weil existence and uniqueness, conditional on
local pinned presentations, generic pair descent and normal-idempotent
factor rigidity. No assertion of those three inputs is made here. -/
def affineAdjointWeilRestriction_of_inputs
    (hlocal : ∀ M : AffineAdjointPinnedModel.{u}, IsFibrewiseNontrivial M.group →
      Nonempty (AffineAdjointWeilPresentation M.group))
    (hD : AffineWeilPairEtaleDescentStatement.{u})
    (hR : WeilFactorIdempotentRigidityStatement.{u}) :
    AffineAdjointWeilRestrictionStatement.{u} := by
  intro A _ G hG hadj hnt
  refine ⟨(AffineAdjointWeilPresentation.ofPinnedCharts hD hlocal G hG hadj hnt).exists_pair, ?_⟩
  intro B B'' _ _ _ _ _ _ _ _ _ _ G' G'' _ _ _ _ hred' hred'' h' h'' ⟨e₁⟩ ⟨e₂⟩
  exact WeilFactor.exists_baseChange_iso_of_weilRestriction_iso hR
    hred' (fun s => (h' s).2) hred'' (fun s => (h'' s).2) (e₁.symm ≪≫ e₂)

end Langlands.GroupScheme
