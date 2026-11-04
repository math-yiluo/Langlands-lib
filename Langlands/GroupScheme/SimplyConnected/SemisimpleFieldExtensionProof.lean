import Langlands.GroupScheme.SimplyConnected.FieldExtensionStatement
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Reductive.FiniteCenterBaseChange

/-! # Semisimplicity under arbitrary field extension -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Arbitrary field extension preserves semisimplicity of an actual group scheme. -/
theorem isSemisimpleFieldExtension : IsSemisimpleFieldExtensionStatement.{u} := by
  intro k K _ _ _ G hG
  exact ⟨connectedReductiveFieldExtensionStatement k K G hG.isConnectedReductive,
    hG.hasFiniteCenter.baseChange (algebraBaseMap k K)⟩

end Langlands.GroupScheme
