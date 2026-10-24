import Langlands.Shimura.Unitary.GaloisEmbeddingMatrices
import Mathlib.Algebra.BigOperators.Pi

noncomputable section
open NumberField Module Algebra
open scoped TensorProduct Classical BigOperators

namespace Langlands.Shimura
namespace ComplexMatrix

/-- A matrix supported at exactly one embedding factor. -/
def singleFactor {I M : Type*} [Zero M] (i : I) (m : M) : I → M :=
  fun j => if j = i then m else 0

@[simp] theorem singleFactor_same {I M : Type*} [Zero M] (i : I) (m : M) :
    singleFactor i m i = m := by simp [singleFactor]

@[simp] theorem singleFactor_ne {I M : Type*} [Zero M] {i j : I} (h : j ≠ i) (m : M) :
    singleFactor i m j = 0 := by simp [singleFactor, h]

theorem sum_singleFactor {I M : Type*} [Fintype I] [AddCommMonoid M] (x : I → M) :
    ∑ i, singleFactor i (x i) = x := by
  funext j
  simp [singleFactor, Finset.sum_apply]

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

open ComplexMatrix

/-- A single input factor has zero image at every embedding except its Galois image. -/
theorem embeddingMatrixGaloisEquiv_single_zero (s : ℂ ≃ₐ[ℚ] ℂ)
    (i j : K →+* ℂ) (hji : j ≠ (s : ℂ →+* ℂ).comp i)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    C.embeddingMatrixGaloisEquiv hΦ b s (singleFactor i M) j = 0 := by
  obtain ⟨k, hk⟩ : ∃ k : K, j k ≠ s (i k) := by
    by_contra h
    push Not at h
    exact hji (RingHom.ext h)
  have hmul : (fun l : K →+* ℂ => Matrix.scalar (Fin n) (l k)) * singleFactor i M =
      i k • singleFactor i M := by
    funext l
    by_cases hl : l = i
    · subst l
      simp only [Pi.mul_apply, singleFactor_same, Pi.smul_apply]
      exact (Algebra.smul_def (i k) M).symm
    · simp [singleFactor, hl]
  have ht := congrArg (C.embeddingMatrixGaloisEquiv hΦ b s) hmul
  rw [map_mul, embeddingMatrixGaloisEquiv_center, embeddingMatrixGaloisEquiv_smul] at ht
  have hj := congrFun ht j
  change Matrix.scalar (Fin n) (j k) * _ = s (i k) • _ at hj
  have hj' : j k • C.embeddingMatrixGaloisEquiv hΦ b s (singleFactor i M) j =
      s (i k) • C.embeddingMatrixGaloisEquiv hΦ b s (singleFactor i M) j :=
    (Algebra.smul_def _ _).trans hj
  have hz : (j k - s (i k)) •
      C.embeddingMatrixGaloisEquiv hΦ b s (singleFactor i M) j = 0 := by
    rw [sub_smul, hj', sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hk)

/-- The output at the transformed embedding depends only on the original factor. -/
theorem embeddingMatrixGaloisEquiv_factor (s : ℂ ≃ₐ[ℚ] ℂ) (i : K →+* ℂ)
    (x : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) :
    C.embeddingMatrixGaloisEquiv hΦ b s x ((s : ℂ →+* ℂ).comp i) =
      C.embeddingMatrixGaloisEquiv hΦ b s (singleFactor i (x i))
        ((s : ℂ →+* ℂ).comp i) := by
  calc
    _ = C.embeddingMatrixGaloisEquiv hΦ b s (∑ l, singleFactor l (x l))
        ((s : ℂ →+* ℂ).comp i) := by rw [sum_singleFactor]
    _ = ∑ l, C.embeddingMatrixGaloisEquiv hΦ b s (singleFactor l (x l))
        ((s : ℂ →+* ℂ).comp i) := by rw [map_sum, Finset.sum_apply]
    _ = _ := by
      apply Fintype.sum_eq_single i
      intro l hl
      apply C.embeddingMatrixGaloisEquiv_single_zero hΦ b s l
      intro he
      exact hl ((complexEmbeddingGaloisAction K s).injective he.symm)

/-- The ring map from a factor to the factor labelled by its Galois transform. -/
def embeddingFactorGaloisHom (s : ℂ ≃ₐ[ℚ] ℂ) (i : K →+* ℂ) :
    Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) ℂ where
  toFun M := C.embeddingMatrixGaloisEquiv hΦ b s (singleFactor i M)
    ((s : ℂ →+* ℂ).comp i)
  map_one' := by
    have h := C.embeddingMatrixGaloisEquiv_factor hΦ b s i 1
    rw [map_one] at h
    exact h.symm
  map_mul' M N := by
    have he : singleFactor i (M * N) = singleFactor i M * singleFactor i N := by
      funext j
      by_cases h : j = i <;> simp [singleFactor, h]
    rw [he, map_mul]
    rfl
  map_zero' := by
    have he : singleFactor i (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
      funext j; simp [singleFactor]
    rw [he, map_zero]
    rfl
  map_add' M N := by
    have he : singleFactor i (M + N) = singleFactor i M + singleFactor i N := by
      funext j
      by_cases h : j = i <;> simp [singleFactor, h]
    rw [he, map_add]
    rfl

/-- Factorwise form of the full matrix transport. -/
theorem embeddingFactorGaloisHom_apply (s : ℂ ≃ₐ[ℚ] ℂ) (i : K →+* ℂ)
    (x : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) :
    C.embeddingFactorGaloisHom hΦ b s i (x i) =
      C.embeddingMatrixGaloisEquiv hΦ b s x ((s : ℂ →+* ℂ).comp i) :=
  (C.embeddingMatrixGaloisEquiv_factor hΦ b s i x).symm

/-- Each transported factor map is semilinear for the same automorphism. -/
theorem embeddingFactorGaloisHom_smul (s : ℂ ≃ₐ[ℚ] ℂ) (i : K →+* ℂ)
    (z : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    C.embeddingFactorGaloisHom hΦ b s i (z • M) =
      s z • C.embeddingFactorGaloisHom hΦ b s i M := by
  have he : singleFactor i (z • M) = z • singleFactor i M := by
    funext j
    by_cases h : j = i <;> simp [singleFactor, h]
  change C.embeddingMatrixGaloisEquiv hΦ b s (singleFactor i (z • M)) _ = _
  rw [he, embeddingMatrixGaloisEquiv_smul]
  rfl

/-- On original algebra elements the transported chart is the chart at the transformed embedding. -/
theorem embeddingFactorGaloisHom_evaluation (s : ℂ ≃ₐ[ℚ] ℂ) (i : K →+* ℂ) (a : A) :
    C.embeddingFactorGaloisHom hΦ b s i (C.embeddingEvaluation hΦ b i a) =
      C.embeddingEvaluation hΦ b ((s : ℂ →+* ℂ).comp i) a := by
  rw [C.embeddingFactorGaloisHom_apply hΦ b s i (fun j => C.embeddingEvaluation hΦ b j a),
    embeddingMatrixGaloisEquiv_evaluation]

/-- The transported factor homomorphism is injective by support separation. -/
theorem embeddingFactorGaloisHom_injective (s : ℂ ≃ₐ[ℚ] ℂ) (i : K →+* ℂ) :
    Function.Injective (C.embeddingFactorGaloisHom hΦ b s i) := by
  intro M N h
  have ht : C.embeddingMatrixGaloisEquiv hΦ b s (singleFactor i M) =
      C.embeddingMatrixGaloisEquiv hΦ b s (singleFactor i N) := by
    funext j
    by_cases hj : j = (s : ℂ →+* ℂ).comp i
    · subst j; exact h
    · rw [C.embeddingMatrixGaloisEquiv_single_zero hΦ b s i j hj M,
        C.embeddingMatrixGaloisEquiv_single_zero hΦ b s i j hj N]
  have hs := (C.embeddingMatrixGaloisEquiv hΦ b s).injective ht
  simpa only [singleFactor_same] using congrFun hs i

/-- Surjectivity follows by taking a preimage of a matrix supported in the target factor. -/
theorem embeddingFactorGaloisHom_surjective (s : ℂ ≃ₐ[ℚ] ℂ) (i : K →+* ℂ) :
    Function.Surjective (C.embeddingFactorGaloisHom hΦ b s i) := by
  intro N
  let x := (C.embeddingMatrixGaloisEquiv hΦ b s).symm
    (singleFactor ((s : ℂ →+* ℂ).comp i) N)
  refine ⟨x i, ?_⟩
  rw [embeddingFactorGaloisHom_apply]
  change C.embeddingMatrixGaloisEquiv hΦ b s
    ((C.embeddingMatrixGaloisEquiv hΦ b s).symm _) _ = _
  rw [RingEquiv.apply_symm_apply, singleFactor_same]

/-- The actual semilinear ring equivalence between the Galois-related matrix factors. -/
def embeddingFactorGaloisEquiv (s : ℂ ≃ₐ[ℚ] ℂ) (i : K →+* ℂ) :
    Matrix (Fin n) (Fin n) ℂ ≃+* Matrix (Fin n) (Fin n) ℂ :=
  RingEquiv.ofBijective (C.embeddingFactorGaloisHom hΦ b s i)
    ⟨C.embeddingFactorGaloisHom_injective hΦ b s i,
      C.embeddingFactorGaloisHom_surjective hΦ b s i⟩

@[simp] theorem embeddingFactorGaloisEquiv_apply (s : ℂ ≃ₐ[ℚ] ℂ)
    (i : K →+* ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    C.embeddingFactorGaloisEquiv hΦ b s i M = C.embeddingFactorGaloisHom hΦ b s i M := rfl

end HarrisSignatureCharts
end Langlands.Shimura
