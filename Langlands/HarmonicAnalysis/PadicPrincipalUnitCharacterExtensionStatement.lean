import Langlands.HarmonicAnalysis.Conductor
import Langlands.LocalField.Uniformizer

/-! Finite-order extension from actual p-adic principal units. -/

namespace Langlands.HarmonicAnalysis

universe u

/-- Every continuous complex character on an actual principal-unit subgroup
extends with finite order and value one at the supplied uniformizer. -/
def PadicPrincipalUnitCharacterExtensionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (η : T.principalUnits n →ₜ* ℂˣ),
      ∃ χ : F.Carrierˣ →ₜ* ℂˣ,
        (∃ m : ℕ, 0 < m ∧ χ ^ m = 1) ∧
        (∀ z : T.principalUnits n, χ (z : F.Carrierˣ) = η z) ∧
        χ (LocalFactor.PadicAbelian.uniformizerUnit T) = 1

end Langlands.HarmonicAnalysis
