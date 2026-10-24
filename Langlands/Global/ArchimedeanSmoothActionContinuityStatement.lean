import Langlands.Global.ArchimedeanSmoothTopology

/-! # Joint continuity of the actual smooth right action -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The published right regular action is jointly continuous for the
derivative compact-open topology on the actual smooth functions. -/
def SmoothRightActionContinuityStatement : Prop :=
  Continuous (fun p :
    Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K) ×
      DerivativeSmoothFunctions K n =>
    (DerivativeSmoothFunctions.toSmooth K n).symm
      (smoothRightAction K n p.1 (DerivativeSmoothFunctions.toSmooth K n p.2)))

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @SmoothRightActionContinuityStatement

end Langlands.Global.ArchimedeanGL
