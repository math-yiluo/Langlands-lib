import Langlands.Representation.Derivative.MirabolicMinus

/-!
# Joint detection by the actual one-step mirabolic minus functors

This proposition isolates a consequence of the general exact sequence in
Bernstein–Zelevinsky 1977, Proposition 3.2(e). No proof is supplied.
-/

noncomputable section

namespace Langlands.Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Vanishing of both actual one-step minus quotients forces the smooth source
representation of `P_(n+2)` to vanish. -/
def MirabolicOneStepDetection : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (n : ℕ)
    (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear.mirabolic (n + 1) F.Carrier)),
    Subsingleton ((Mirabolic.psiMinus T (n + 1)).obj A) →
    Subsingleton ((Mirabolic.phiMinus T ψ n).obj A) →
    Subsingleton A

end Langlands.Derivative
