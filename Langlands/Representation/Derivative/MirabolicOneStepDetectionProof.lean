import Langlands.Representation.Derivative.MirabolicOneStepDetectionStatement
import Langlands.Representation.Derivative.MinusVanishing

/-!
# Joint detection by the actual one-step mirabolic minus functors

The published relation-span and finite-averaging theorem proves the unchanged
one-step detection proposition for arbitrary smooth representations.
-/

noncomputable section

namespace Langlands.Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Vanishing of both actual one-step minus quotients forces the source to vanish. -/
theorem mirabolicOneStepDetection : MirabolicOneStepDetection.{uF, uV} F T := by
  let := T.topology
  exact fun ψ n A => Mirabolic.subsingleton_of_psiMinus_phiMinus.{uF, uV} T ψ n A

end Langlands.Derivative
