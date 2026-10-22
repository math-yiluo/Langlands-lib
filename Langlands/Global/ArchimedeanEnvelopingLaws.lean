import Langlands.Global.ArchimedeanEnvelopingAction

/-! # Left-translation compatibility for the actual enveloping action -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Every genuine enveloping differential operator commutes with left pullback. -/
def EnvelopingLeftTranslation : Prop :=
  ∀ (u : EnvelopingAlgebra K n)
    (a : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)),
    envelopingAction K n u * smoothLeftTranslation K n a =
      smoothLeftTranslation K n a * envelopingAction K n u

end Langlands.Global.ArchimedeanGL
