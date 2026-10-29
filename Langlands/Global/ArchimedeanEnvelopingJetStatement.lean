import Langlands.Global.ArchimedeanEnvelopingAction

/-! # From genuine enveloping vanishing to ambient matrix zero jets -/

noncomputable section
universe u
open scoped Classical Matrix.Norms.Operator
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

/-- Vanishing of every actual enveloping derivative at one point forces
the whole ambient real matrix jet to vanish there. -/
def EnvelopingZeroJetStatement
    (K : Type u) [Field K] [NumberField K] (n : ℕ) : Prop :=
  ∀ (f : SmoothFunctions K n)
    (x₀ : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)),
    (∀ a : EnvelopingAlgebra K n, (envelopingAction K n a f).val x₀ = 0) →
    ∀ m : ℕ, iteratedFDeriv ℝ m (coordinateExtension K n f)
      (archimedeanGLCoordinates K n x₀ : ArchimedeanMatrix K n) = 0

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @EnvelopingZeroJetStatement

end Langlands.Global.ArchimedeanGL
