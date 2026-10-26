import Langlands.Global.ArchimedeanCompactLieAlgebra
import Langlands.Global.ArchimedeanCompact
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! # Curves in the actual compact subgroup with prescribed real tangent -/

noncomputable section

universe u

open scoped Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

/-- Every skew-adjoint real matrix direction is the derivative at zero of
a curve through the identity in the actual standard compact subgroup. -/
def CompactTangentCurveStatement (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    Prop :=
  ∀ X : compactLieSubalgebra K n,
    ∃ c : ℝ → standardInfiniteCompact K n,
      c 0 = 1 ∧
        HasDerivAt
          (fun t : ℝ =>
            (archimedeanGLCoordinates K n (c t).val : ArchimedeanMatrix K n))
          (realLieAlgebraToMatrix K n (X : RealLieAlgebra K n)) 0

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @CompactTangentCurveStatement

end Langlands.Global.ArchimedeanGL
