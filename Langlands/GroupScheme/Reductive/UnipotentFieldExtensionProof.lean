import Langlands.GroupScheme.Reductive.UnipotentFieldExtensionStatement
import Langlands.GroupScheme.Unipotent.BaseChange

/-! # Preservation of unipotence under field extension: proof -/

universe u

namespace Langlands.GroupScheme

/-- Unipotence of an affine group scheme over a field is preserved by every field extension.
The finite-type hypothesis of the statement is not used. -/
theorem unipotentFieldExtensionStatement : UnipotentFieldExtensionStatement.{u} := by
  intro k K _ _ _ G hG _ hU
  exact IsUnipotent.baseChange hU

end Langlands.GroupScheme
