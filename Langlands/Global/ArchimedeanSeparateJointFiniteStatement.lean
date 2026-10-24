import Langlands.Global.ArchimedeanJointFinite

/-! # Combining separate center and compact differential finiteness -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Finiteness of both commuting differential orbits gives finiteness of their
joint orbit on the same actual smooth function. -/
def SeparateJointFiniteStatement : Prop :=
  ∀ f : SmoothFunctions K n,
    IsCenterFinite K n f → IsCompactLieFinite K n f → IsJointFinite K n f

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @SeparateJointFiniteStatement

end Langlands.Global.ArchimedeanGL
