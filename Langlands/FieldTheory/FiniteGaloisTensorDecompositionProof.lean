import Langlands.FieldTheory.FiniteGaloisTensorDecompositionStatement
import Langlands.Algebra.SeparableTensorProof

/-! # Proof of the explicit decomposition of `L ⊗[k] L` for a finite Galois extension -/

namespace Langlands.FieldTheory

universe u

open scoped TensorProduct

/-- For a finite Galois extension `L/k`, evaluation at the automorphisms is an `L`-algebra
equivalence `L ⊗[k] L ≃ₐ[L] (Gal(L/k) → L)` sending `a ⊗ₜ b` to `σ ↦ a * σ b`. -/
theorem finiteGaloisTensorDecomposition : FiniteGaloisTensorDecompositionStatement.{u} := by
  intro k L _ _ _ _ _
  have hbij := Langlands.Algebra.SeparableTensor.embeddingEvaluationStatement.{u,u,u} k L L
    (Normal.splits inferInstance)
  refine ⟨(AlgEquiv.ofBijective _ hbij).trans
    (AlgEquiv.piCongrLeft' L (fun _ => L) (algEquivEquivAlgHom k L).toEquiv.symm), ?_⟩
  intro a b σ
  rfl

end Langlands.FieldTheory
