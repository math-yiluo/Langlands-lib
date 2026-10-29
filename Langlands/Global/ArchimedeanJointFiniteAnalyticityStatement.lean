import Langlands.Global.ArchimedeanJointFinite
import Langlands.Global.ArchimedeanSmoothDifferential
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Real analyticity from the actual finite joint differential orbit -/

noncomputable section
universe u
open scoped Classical Matrix.Norms.Operator
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

/-- Finite genuine joint central-and-compact differential orbit implies real analyticity
at every actual matrix unit. -/
def JointFiniteAnalyticityStatement
    (K : Type u) [Field K] [NumberField K] (n : ℕ) : Prop :=
  ∀ f : SmoothFunctions K n, IsJointFinite K n f →
    ∀ g : ArchimedeanGL K n,
      AnalyticAt ℝ (coordinateExtension K n f) (g : ArchimedeanMatrix K n)

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @JointFiniteAnalyticityStatement

end Langlands.Global.ArchimedeanGL
