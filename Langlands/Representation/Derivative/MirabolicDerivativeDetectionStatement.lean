import Langlands.Representation.Derivative.Homogeneity

/-!
# Positive-order detection for every smooth mirabolic representation

This proposition records the detection consequence of the general derivative
filtration in Bernstein–Zelevinsky 1977, section 3.5. No proof is supplied.
-/

noncomputable section

namespace Langlands.Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every nonzero smooth representation of `P_(N+1)` has positive derivative level. -/
def MirabolicDerivativeDetection : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N : ℕ) (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear.mirabolic N F.Carrier)),
    Nontrivial A → 0 < level T ψ A

end Langlands.Derivative
