import Langlands.Representation.Derivative.MirabolicMinus
import Langlands.Representation.Unitary.Basic

/-!
# Unitarity under normalized mirabolic Phi-minus

The forward implication furnished by the positive Hermitian form correspondence
in Bernstein 1984, §9.3(ii). This module states the implication; it does not prove it.
-/

noncomputable section

namespace Langlands.Derivative

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

/-- Normalized `Φ⁻ : P_(n+2) → P_(n+1)` preserves unitarizability.
No finite-length or homogeneity hypothesis is needed for this direction. -/
def MirabolicPhiMinusUnitarity : Prop :=
  letI := T.topology
  ∀ (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ)
    (X : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (n + 1) F.Carrier)),
    IsUnitarizable X.representation →
      IsUnitarizable ((Mirabolic.phiMinus T ψ n).obj X).representation

end Langlands.Derivative
