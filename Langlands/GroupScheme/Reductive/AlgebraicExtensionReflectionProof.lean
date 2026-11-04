import Langlands.GroupScheme.Reductive.AlgebraicExtensionReflectionStatement
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof

/-! # Reflection along algebraic field extensions -/

universe u

namespace Langlands.GroupScheme

/-- Connected reductivity is reflected by every algebraic field extension. -/
theorem connectedReductiveAlgebraicExtensionReflection :
    ConnectedReductiveAlgebraicExtensionReflectionStatement.{u} := by
  intro k K _ _ _ _ G hG
  exact IsConnectedReductive.of_fieldExtension hG

/-- Semisimplicity is reflected by every algebraic field extension. -/
theorem semisimpleAlgebraicExtensionReflection :
    SemisimpleAlgebraicExtensionReflectionStatement.{u} := by
  intro k K _ _ _ _ G hG
  exact IsSemisimple.of_fieldExtension hG

/-- The published package of both algebraic-extension reflection statements. -/
theorem algebraicExtensionReflection : AlgebraicExtensionReflectionStatement.{u} :=
  ⟨connectedReductiveAlgebraicExtensionReflection,
    semisimpleAlgebraicExtensionReflection⟩

end Langlands.GroupScheme
