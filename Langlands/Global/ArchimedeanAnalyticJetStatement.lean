import Langlands.Global.ArchimedeanSmoothDifferential
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Connected.Basic

/-! # Analytic uniqueness from vanishing actual matrix jets -/

noncomputable section
universe u
open scoped Classical Matrix.Norms.Operator
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

/-- An analytic smooth function whose full ambient jet vanishes at one
point vanishes on that point's connected component. -/
def AnalyticMatrixJetUniquenessStatement
    (K : Type u) [Field K] [NumberField K] (n : ℕ) : Prop :=
  ∀ (f : SmoothFunctions K n)
    (x₀ : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)),
    (∀ g : ArchimedeanGL K n,
      AnalyticAt ℝ (coordinateExtension K n f) (g : ArchimedeanMatrix K n)) →
    (∀ m : ℕ, iteratedFDeriv ℝ m (coordinateExtension K n f)
      (archimedeanGLCoordinates K n x₀ : ArchimedeanMatrix K n) = 0) →
    ∀ x ∈ connectedComponent x₀, f.val x = 0

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @AnalyticMatrixJetUniquenessStatement

end Langlands.Global.ArchimedeanGL
