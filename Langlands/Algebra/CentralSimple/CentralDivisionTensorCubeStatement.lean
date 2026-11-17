import Mathlib.Algebra.Central.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.RingTheory.TensorProduct.Basic

/-! # A tensor-cube obstruction for central division algebras of degree six -/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.CentralSimple

/-- A central division algebra of reduced degree six cannot have a split tensor
cube. The tensor product and the matrix-algebra isomorphism are actual algebras.
This arithmetic statement is unproved. -/
def CentralDivisionDegreeSixTensorCubeNonSplitStatement : Prop :=
  ∀ (k : Type u) [Field k] (D : Type u) [DivisionRing D] [Algebra k D]
    [FiniteDimensional k D] [Algebra.IsCentral k D],
    Module.finrank k D = 36 →
    ∀ (n : ℕ), 0 < n →
      ¬ Nonempty (((D ⊗[k] D) ⊗[k] D) ≃ₐ[k] Matrix (Fin n) (Fin n) k)

end Langlands.CentralSimple
