import Langlands.GroupScheme.Reductive.FiniteFieldFormExistenceStatement
import Langlands.GroupScheme.Reductive.FiniteFieldFormConstruction

/-! # Every finite-order based automorphism is the class of a finite-field form -/

noncomputable section

universe u

namespace Langlands.GroupScheme

/-- Every finite-order based automorphism occurs as the Frobenius class of a form. -/
theorem finiteFieldFormExistence : FiniteFieldFormExistenceStatement.{u} := by
  intro k _ _ G₀ _ p θ hθ
  let F := p.finiteFieldForm θ hθ
  exact ⟨F.group, inferInstance, inferInstance, F.pinningData, F.rootEquiv,
    F.preserves_base, F.frobenius⟩

end Langlands.GroupScheme
