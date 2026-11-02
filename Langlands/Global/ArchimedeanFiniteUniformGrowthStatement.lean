import Langlands.Global.ArchimedeanCompact
import Langlands.Global.ArchimedeanCenterFinite
import Langlands.Global.ArchimedeanGrowth

/-! # A common matrix-height exponent for all enveloping derivatives -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Every supplied matrix-height exponent for a compact-finite, center-finite
smooth function also bounds all of its actual enveloping derivatives.
The multiplicative constant may depend on the enveloping element. -/
def FiniteUniformDifferentialGrowthStatement : Prop :=
  ∀ (f : SmoothFunctions K n),
    Langlands.FiniteVectors.IsFiniteVector
      ((smoothRightAction K n).comp (standardInfiniteCompact K n).subtype) f →
    IsCenterFinite K n f →
    ∀ (C : ℝ), 0 ≤ C → ∀ (d : ℕ),
    (∀ g, ‖f.val g‖ ≤ C * matrixHeight K n g ^ d) →
    ∀ a : EnvelopingAlgebra K n, ∃ D : ℝ, 0 ≤ D ∧
      ∀ g, ‖(envelopingAction K n a f).val g‖ ≤ D * matrixHeight K n g ^ d

end Langlands.Global.ArchimedeanGL
