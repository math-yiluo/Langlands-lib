import Langlands.Shimura.Unitary.CMEmbeddingIndices
import Langlands.Shimura.Unitary.ComplexMatrixSplitting

noncomputable section
open NumberField Module Algebra
open scoped TensorProduct Classical

namespace Langlands.Shimura

namespace ComplexMatrix

/-- Separate the ordered pair of factors with true denoting the first factor. -/
def factorIndexEquiv (R M I : Type*) [CommRing R] [Ring M] [Algebra R M] :
    (I → M × M) ≃ₐ[R] ((I × Bool) → M) where
  toFun x p := if p.2 then (x p.1).1 else (x p.1).2
  invFun y i := (y (i, true), y (i, false))
  left_inv x := rfl
  right_inv y := by funext ⟨i, b⟩; cases b <;> rfl
  map_mul' x y := by funext ⟨i, b⟩; cases b <;> rfl
  map_add' x y := by funext ⟨i, b⟩; cases b <;> rfl
  commutes' r := by funext ⟨i, b⟩; cases b <;> rfl

end ComplexMatrix

namespace HarrisSignatureCharts

universe u v w z
variable {E : Type u} {K : Type v} {A : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {σ : SecondKindInvolution E K A} {n : ℕ}
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts σ n Φ) (hΦ : IsCMSection E K Φ)
  {ι : Type z} [Fintype ι] (b : Basis ι E A)

/-- The actual rational complex scalar extension with factors labelled by CM embeddings. -/
def embeddingMatrixEquiv : ℂ ⊗[ℚ] A ≃ₐ[ℂ]
    ((K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) :=
  (C.complexMatrixEquiv b).trans
    ((ComplexMatrix.factorIndexEquiv ℂ (Matrix (Fin n) (Fin n) ℂ) (E →+* ℝ)).trans
      (AlgEquiv.piCongrLeft ℂ (fun _ : K →+* ℂ => Matrix (Fin n) (Fin n) ℂ)
        (cmFactorEmbeddingEquiv Φ hΦ)))

@[simp] theorem embeddingMatrixEquiv_factor (x : ℂ ⊗[ℚ] A)
    (p : (E →+* ℝ) × Bool) :
    C.embeddingMatrixEquiv hΦ b x (cmFactorEmbedding Φ p) =
      if p.2 then (C.complexMatrixEquiv b x p.1).1
      else (C.complexMatrixEquiv b x p.1).2 := by
  change Equiv.piCongrLeft (fun _ : K →+* ℂ => Matrix (Fin n) (Fin n) ℂ)
    (cmFactorEmbeddingEquiv Φ hΦ)
    (ComplexMatrix.factorIndexEquiv ℂ (Matrix (Fin n) (Fin n) ℂ) (E →+* ℝ)
      (C.complexMatrixEquiv b x)) (cmFactorEmbeddingEquiv Φ hΦ p) = _
  rw [Equiv.piCongrLeft_apply_apply]
  rfl

/-- The original algebra evaluated at the matrix factor labelled by an embedding. -/
def embeddingEvaluation (i : K →+* ℂ) : A →+* Matrix (Fin n) (Fin n) ℂ :=
  ((Pi.evalRingHom _ i).comp (C.embeddingMatrixEquiv hΦ b).toRingHom).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] ℂ ⊗[ℚ] A).toRingHom

@[simp] theorem embeddingEvaluation_factor (a : A) (p : (E →+* ℝ) × Bool) :
    C.embeddingEvaluation hΦ b (cmFactorEmbedding Φ p) a =
      if p.2 then C.evaluation a p.1 else (C.evaluation a p.1).map star := by
  change C.embeddingMatrixEquiv hΦ b ((1 : ℂ) ⊗ₜ[ℚ] a) (cmFactorEmbedding Φ p) = _
  rw [embeddingMatrixEquiv_factor, complexMatrixEquiv_tmul]
  simp

/-- The complex scalar is multiplied into each embedding-labelled factor. -/
@[simp] theorem embeddingMatrixEquiv_tmul (z : ℂ) (a : A) (i : K →+* ℂ) :
    C.embeddingMatrixEquiv hΦ b (z ⊗ₜ[ℚ] a) i =
      z • C.embeddingEvaluation hΦ b i a := by
  obtain ⟨p, rfl⟩ := (cmFactorEmbeddingEquiv Φ hΦ).surjective i
  change C.embeddingMatrixEquiv hΦ b (z ⊗ₜ[ℚ] a) (cmFactorEmbedding Φ p) = _
  rw [embeddingMatrixEquiv_factor, complexMatrixEquiv_tmul]
  change (if p.2 then z • C.evaluation a p.1 else z • (C.evaluation a p.1).map star) = _
  rw [cmFactorEmbeddingEquiv_apply, embeddingEvaluation_factor]
  cases p.2 <;> rfl

/-- The center acts in the factor labelled by `i` through the embedding `i`. -/
theorem embeddingEvaluation_center (i : K →+* ℂ) (k : K) :
    C.embeddingEvaluation hΦ b i (algebraMap K A k) = Matrix.scalar (Fin n) (i k) := by
  obtain ⟨⟨τ, q⟩, rfl⟩ := (cmFactorEmbeddingEquiv Φ hΦ).surjective i
  change C.embeddingEvaluation hΦ b (cmFactorEmbedding Φ (τ, q)) (algebraMap K A k) = _
  rw [embeddingEvaluation_factor, C.evaluation_center]
  cases q
  · change (Matrix.scalar (Fin n) (Φ τ k)).map star =
      Matrix.scalar (Fin n) (star (Φ τ k))
    ext r c
    by_cases h : r = c <;> simp [Matrix.scalar, Matrix.diagonal, h]
  · rfl

end HarrisSignatureCharts
end Langlands.Shimura
