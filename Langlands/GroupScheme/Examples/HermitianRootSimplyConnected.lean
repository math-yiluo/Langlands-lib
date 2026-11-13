import Langlands.GroupScheme.Examples.HermitianRootSplitting
import Langlands.GroupScheme.SimplyConnected.AlgebraicExtensionReflection
import Langlands.GroupScheme.SpecialLinearSimplyConnected

/-! # Simple connectedness of the weighted Hermitian group scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.HermitianRoot.SchemeModel

open SU3Root Langlands.Shimura.AlgebraInvolution.SchemeModel

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {Middle : Type} [Fintype Middle] [DecidableEq Middle]
  (H : DiagonalForm (fieldInvolution k L) Middle)
  (w : Middle → Lˣ) (hw : ∀ i, (w i : L) = H.weight i)

/-- **Simple connectedness.** The weighted Hermitian group scheme `SU(H)` over `k` is simply
connected: after the quadratic scalar extension to `L` it becomes the special linear group, which
is simply connected, and simple connectedness reflects along algebraic field extensions. -/
theorem isSimplyConnected : IsSimplyConnected (groupScheme k L H w hw) := by
  have : Module.Finite k L :=
    Module.finite_of_finrank_eq_succ (Algebra.IsQuadraticExtension.finrank_eq_two k L)
  have : Algebra.IsAlgebraic k L := Algebra.IsAlgebraic.of_finite k L
  exact IsSimplyConnected.of_algebraicExtension (K := L)
    ((SpecialLinear.isSimplyConnected (Index Middle) L).of_iso (splittingIso k L H w hw))

end Langlands.GroupScheme.HermitianRoot.SchemeModel
