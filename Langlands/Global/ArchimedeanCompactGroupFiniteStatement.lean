import Langlands.Global.ArchimedeanJointFinite
import Langlands.Global.ArchimedeanCompact

/-! # From compact group finiteness to compact differential finiteness -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Finite orbit under the actual standard compact subgroup implies finite orbit
under the actual compact-generated enveloping subalgebra. -/
def CompactGroupFiniteDifferentialStatement : Prop :=
  ∀ f : SmoothFunctions K n,
    Langlands.FiniteVectors.IsFiniteVector
      ((smoothRightAction K n).comp (standardInfiniteCompact K n).subtype) f →
    IsCompactLieFinite K n f

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @CompactGroupFiniteDifferentialStatement

end Langlands.Global.ArchimedeanGL
