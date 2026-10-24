import Langlands.Shimura.Unitary.ComplexEmbeddingMatrices

noncomputable section
open NumberField Module Algebra
open scoped TensorProduct Classical

namespace Langlands.Shimura
namespace ComplexMatrix

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The actual coefficient automorphism on the rational complex scalar extension. -/
def coefficientEquiv (s : ℂ ≃ₐ[ℚ] ℂ) : ℂ ⊗[ℚ] A ≃ₐ[ℚ] ℂ ⊗[ℚ] A :=
  Algebra.TensorProduct.congr s (AlgEquiv.refl : A ≃ₐ[ℚ] A)

@[simp] theorem coefficientEquiv_tmul (s : ℂ ≃ₐ[ℚ] ℂ) (z : ℂ) (a : A) :
    coefficientEquiv s (z ⊗ₜ[ℚ] a) = s z ⊗ₜ[ℚ] a := rfl

theorem coefficientEquiv_eq_changeCoefficients (s : ℂ ≃ₐ[ℚ] ℂ) (x : ℂ ⊗[ℚ] A) :
    coefficientEquiv s x = AlgebraInvolution.changeCoefficients s.toAlgHom x := rfl

@[simp] theorem coefficientEquiv_one (x : ℂ ⊗[ℚ] A) :
    coefficientEquiv (1 : ℂ ≃ₐ[ℚ] ℂ) x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul z a => rfl
  | add x y hx hy => rw [map_add, hx, hy]

theorem coefficientEquiv_mul (s t : ℂ ≃ₐ[ℚ] ℂ) (x : ℂ ⊗[ℚ] A) :
    coefficientEquiv (s * t) x = coefficientEquiv s (coefficientEquiv t x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem coefficientEquiv_smul (s : ℂ ≃ₐ[ℚ] ℂ) (z : ℂ) (x : ℂ ⊗[ℚ] A) :
    coefficientEquiv s (z • x) = s z • coefficientEquiv s x := by
  induction x using TensorProduct.inductionOn with
  | tmul w a => simp only [TensorProduct.smul_tmul', smul_eq_mul,
      coefficientEquiv_tmul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

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

/-- Galois coefficient transport expressed in the actual embedding-labelled matrix charts. -/
def embeddingMatrixGaloisEquiv (s : ℂ ≃ₐ[ℚ] ℂ) :
    ((K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) ≃+*
      ((K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) :=
  (C.embeddingMatrixEquiv hΦ b).toRingEquiv.symm.trans
    ((ComplexMatrix.coefficientEquiv (A := A) s).toRingEquiv.trans
      (C.embeddingMatrixEquiv hΦ b).toRingEquiv)

/-- The chart action intertwines the splitting with coefficient change on the tensor algebra. -/
@[simp] theorem embeddingMatrixGaloisEquiv_apply (s : ℂ ≃ₐ[ℚ] ℂ) (x : ℂ ⊗[ℚ] A) :
    C.embeddingMatrixGaloisEquiv hΦ b s (C.embeddingMatrixEquiv hΦ b x) =
      C.embeddingMatrixEquiv hΦ b (ComplexMatrix.coefficientEquiv s x) := by
  change C.embeddingMatrixEquiv hΦ b
    (ComplexMatrix.coefficientEquiv s
      ((C.embeddingMatrixEquiv hΦ b).symm (C.embeddingMatrixEquiv hΦ b x))) = _
  rw [AlgEquiv.symm_apply_apply]

@[simp] theorem embeddingMatrixGaloisEquiv_one
    (x : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) :
    C.embeddingMatrixGaloisEquiv hΦ b 1 x = x := by
  obtain ⟨x, rfl⟩ := (C.embeddingMatrixEquiv hΦ b).surjective x
  rw [embeddingMatrixGaloisEquiv_apply, ComplexMatrix.coefficientEquiv_one]

theorem embeddingMatrixGaloisEquiv_mul (s t : ℂ ≃ₐ[ℚ] ℂ)
    (x : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) :
    C.embeddingMatrixGaloisEquiv hΦ b (s * t) x =
      C.embeddingMatrixGaloisEquiv hΦ b s (C.embeddingMatrixGaloisEquiv hΦ b t x) := by
  obtain ⟨x, rfl⟩ := (C.embeddingMatrixEquiv hΦ b).surjective x
  simp only [embeddingMatrixGaloisEquiv_apply, ComplexMatrix.coefficientEquiv_mul]

/-- The Galois action on the full embedding-labelled matrix algebra. -/
def embeddingMatrixGaloisAction : (ℂ ≃ₐ[ℚ] ℂ) →*
    (((K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) ≃+*
      ((K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ)) where
  toFun := C.embeddingMatrixGaloisEquiv hΦ b
  map_one' := by
    apply RingEquiv.ext
    exact C.embeddingMatrixGaloisEquiv_one hΦ b
  map_mul' s t := by
    apply RingEquiv.ext
    exact C.embeddingMatrixGaloisEquiv_mul hΦ b s t

/-- The matrix-chart transport is semilinear for the given complex automorphism. -/
theorem embeddingMatrixGaloisEquiv_smul (s : ℂ ≃ₐ[ℚ] ℂ) (z : ℂ)
    (x : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) :
    C.embeddingMatrixGaloisEquiv hΦ b s (z • x) =
      s z • C.embeddingMatrixGaloisEquiv hΦ b s x := by
  obtain ⟨x, rfl⟩ := (C.embeddingMatrixEquiv hΦ b).surjective x
  rw [← map_smul, embeddingMatrixGaloisEquiv_apply,
    ComplexMatrix.coefficientEquiv_smul, map_smul, embeddingMatrixGaloisEquiv_apply]

/-- Original algebra elements are fixed by rational coefficient transport. -/
@[simp] theorem embeddingMatrixGaloisEquiv_evaluation (s : ℂ ≃ₐ[ℚ] ℂ) (a : A) :
    C.embeddingMatrixGaloisEquiv hΦ b s (fun i => C.embeddingEvaluation hΦ b i a) =
      fun i => C.embeddingEvaluation hΦ b i a := by
  have he : (fun i => C.embeddingEvaluation hΦ b i a) =
      C.embeddingMatrixEquiv hΦ b ((1 : ℂ) ⊗ₜ[ℚ] a) := by
    funext i
    rw [embeddingMatrixEquiv_tmul, one_smul]
  rw [he, embeddingMatrixGaloisEquiv_apply, ComplexMatrix.coefficientEquiv_tmul, map_one]

/-- The center-valued embedding function is fixed by the actual chart transport. -/
theorem embeddingMatrixGaloisEquiv_center (s : ℂ ≃ₐ[ℚ] ℂ) (k : K) :
    C.embeddingMatrixGaloisEquiv hΦ b s (fun i => Matrix.scalar (Fin n) (i k)) =
      fun i => Matrix.scalar (Fin n) (i k) := by
  simpa only [embeddingEvaluation_center] using
    C.embeddingMatrixGaloisEquiv_evaluation hΦ b s (algebraMap K A k)

end HarrisSignatureCharts
end Langlands.Shimura
