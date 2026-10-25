import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Equiv

/-! Field-linear automorphisms of full matrix algebras are inner (statement). -/

namespace Langlands.MatrixAlgebra

universe uk uI

/-- Milne, *Class Field Theory* (v4.03), Chapter IV, Corollary 2.12, for the full
matrix algebra `Matrix I I k` over a field `k`: every `k`-algebra automorphism `e`
is conjugation by a unit `U`, that is `e M = U * M * U⁻¹` for every matrix `M`.
The finite index type `I` may be empty. -/
def AlgEquivIsInnerStatement : Prop :=
  ∀ (k : Type uk) [Field k] (I : Type uI) [Fintype I] [DecidableEq I]
    (e : Matrix I I k ≃ₐ[k] Matrix I I k),
    ∃ U : (Matrix I I k)ˣ, ∀ M : Matrix I I k,
      e M = (U : Matrix I I k) * M * ((U⁻¹ : (Matrix I I k)ˣ) : Matrix I I k)

end Langlands.MatrixAlgebra
