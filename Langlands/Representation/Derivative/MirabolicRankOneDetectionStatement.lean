import Langlands.Representation.Derivative.MirabolicMinus

/-!
# The rank-one boundary of mirabolic derivative detection

This proposition records vanishing detection by the actual normalized `Ψ⁻`
from `P_1` to `GL_0`. It is an elementary boundary assertion, not a proof
of the positive-rank detection sequence.
-/

noncomputable section

namespace Langlands.Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The actual normalized `Ψ⁻` from `P_1` to `GL_0` detects vanishing of
arbitrary smooth source representations. -/
def MirabolicRankOneDetection : Prop :=
  letI := T.topology
  ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear.mirabolic 0 F.Carrier),
    Subsingleton ((Mirabolic.psiMinus T 0).obj A) → Subsingleton A

end Langlands.Derivative
