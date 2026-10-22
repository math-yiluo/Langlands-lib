import Langlands.Global.ArchimedeanGL
import Mathlib.Analysis.Calculus.VectorField

/-!
# Local calculus statements for the archimedean differential

These statements concern the ambient matrix space. They are local at the
evaluation point, so that they apply to smooth functions expressed in a units
chart without assuming a globally smooth extension to all matrices.
-/

noncomputable section

universe u

open scoped Classical ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The matrix directional derivatives have the positive commutator sign for
the right-translation convention `R(g)f(x) = f(x*g)`. -/
def AmbientDifferentialCommutator : Prop :=
  ∀ (f : ArchimedeanMatrix K n → ℂ) (X Y g : ArchimedeanMatrix K n),
    ContDiffAt ℝ 2 f g →
    fderiv ℝ f g (g * (X * Y - Y * X)) =
      fderiv ℝ (fun h => fderiv ℝ f h (h * Y)) g (g * X) -
        fderiv ℝ (fun h => fderiv ℝ f h (h * X)) g (g * Y)

/-- Left multiplication intertwines the matrix directional derivatives; the
matrix multiplying on the left need not be invertible. -/
def AmbientDifferentialLeftTranslation : Prop :=
  ∀ (f : ArchimedeanMatrix K n → ℂ) (a X g : ArchimedeanMatrix K n),
    DifferentiableAt ℝ f (a * g) →
    fderiv ℝ (fun h => f (a * h)) g (g * X) =
      fderiv ℝ f (a * g) ((a * g) * X)

/-- The two local calculus laws needed to assemble the actual group differential. -/
def AmbientDifferentialLaws : Prop :=
  AmbientDifferentialCommutator K n ∧ AmbientDifferentialLeftTranslation K n

end Langlands.Global.ArchimedeanGL
