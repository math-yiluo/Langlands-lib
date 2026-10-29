import Langlands.LocalField.Definitions
import Langlands.HarmonicAnalysis.Basic

/-!
# Existence of a nontrivial unitary additive character

A focused existence target for each supplied p-adic topology. The character is
the existing `UnitaryAdditiveCharacter`. This module states the proposition; a
proof is a separate obligation.
-/

namespace Langlands.HarmonicAnalysis

universe u

/-- Every supplied topological realization of a finite extension of `ℚ_p`
carries a continuous nontrivial unitary additive character. -/
def PadicUnitaryAdditiveCharacterExistsStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  Nonempty (UnitaryAdditiveCharacter F.Carrier)

end Langlands.HarmonicAnalysis
