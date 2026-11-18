import Langlands.Global.AdelicGroupLocalPoints
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct

/-! # The Hasse principle for isometry of quadratic forms over number fields -/

noncomputable section

universe u

namespace Langlands

/-- Two nondegenerate quadratic forms of the same dimension over a number field are
isometric if their scalar extensions to every completion are isometric. -/
def NumberFieldQuadraticIsometryStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F],
    letI : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
    ∀ (n : ℕ) (q₁ q₂ : QuadraticForm F (Fin n → F)),
      q₁.polarBilin.Nondegenerate → q₂.polarBilin.Nondegenerate →
      (∀ v : Global.Place F,
        (q₁.baseChange (Global.placeCompletion F v)).Equivalent
          (q₂.baseChange (Global.placeCompletion F v))) →
      q₁.Equivalent q₂

end Langlands
