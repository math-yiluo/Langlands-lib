import Langlands.Global.AdelicGroupLocalPoints
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct

/-! # Local-to-global isotropy over number fields -/

noncomputable section

universe u

namespace Langlands

/-- A nondegenerate quadratic form over a number field is isotropic if its scalar
extension to every completion is isotropic. -/
def NumberFieldQuadraticIsotropyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F],
    letI : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
    ∀ (V : Type u) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (q : QuadraticForm F V),
      q.polarBilin.Nondegenerate →
      (∀ v : Global.Place F, ¬ (q.baseChange (Global.placeCompletion F v)).Anisotropic) →
      ¬ q.Anisotropic

end Langlands
