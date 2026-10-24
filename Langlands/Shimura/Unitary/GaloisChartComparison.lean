import Langlands.Shimura.Unitary.GaloisMatrixFactors

noncomputable section
open NumberField Module Algebra
open scoped TensorProduct Classical

namespace Langlands.Shimura
namespace ComplexMatrix

/-- Entrywise coefficient change is semilinear for complex scalar multiplication. -/
theorem mapMatrix_smul {n : ℕ} (s : ℂ ≃ₐ[ℚ] ℂ) (z : ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    s.toRingEquiv.mapMatrix (z • M) = s z • s.toRingEquiv.mapMatrix M := by
  ext r c
  exact map_mul s z (M r c)

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

/-- The complex-linear comparison left after removing entrywise Galois transport. -/
def embeddingChartComparison (s : ℂ ≃ₐ[ℚ] ℂ) (i : K →+* ℂ) :
    Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  AlgEquiv.ofRingEquiv
    (f := s.symm.toRingEquiv.mapMatrix.trans (C.embeddingFactorGaloisEquiv hΦ b s i))
    (by
      intro z
      change C.embeddingFactorGaloisEquiv hΦ b s i
        (s.symm.toRingEquiv.mapMatrix (algebraMap ℂ _ z)) = algebraMap ℂ _ z
      rw [Algebra.algebraMap_eq_smul_one, ComplexMatrix.mapMatrix_smul, map_one,
        embeddingFactorGaloisEquiv_apply, embeddingFactorGaloisHom_smul, map_one,
        AlgEquiv.apply_symm_apply])

/-- The comparison first applies the inverse coefficient map, then factor transport. -/
theorem embeddingChartComparison_apply (s : ℂ ≃ₐ[ℚ] ℂ) (i : K →+* ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    C.embeddingChartComparison hΦ b s i M =
      C.embeddingFactorGaloisEquiv hΦ b s i (s.symm.toRingEquiv.mapMatrix M) := rfl

/-- Factor transport is the comparison after entrywise application of the automorphism. -/
theorem embeddingChartComparison_map (s : ℂ ≃ₐ[ℚ] ℂ) (i : K →+* ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    C.embeddingChartComparison hΦ b s i (s.toRingEquiv.mapMatrix M) =
      C.embeddingFactorGaloisEquiv hΦ b s i M := by
  rw [embeddingChartComparison_apply]
  apply congrArg (C.embeddingFactorGaloisEquiv hΦ b s i)
  ext r c
  exact s.symm_apply_apply (M r c)

/-- The comparison matches the Galois-transformed original-algebra evaluations. -/
theorem embeddingChartComparison_evaluation (s : ℂ ≃ₐ[ℚ] ℂ)
    (i : K →+* ℂ) (a : A) :
    C.embeddingChartComparison hΦ b s i
        (s.toRingEquiv.mapMatrix (C.embeddingEvaluation hΦ b i a)) =
      C.embeddingEvaluation hΦ b ((s : ℂ →+* ℂ).comp i) a := by
  rw [embeddingChartComparison_map, embeddingFactorGaloisEquiv_apply,
    embeddingFactorGaloisHom_evaluation]

/-- The full chart action factors into entrywise coefficient change and a linear comparison. -/
theorem embeddingMatrixGaloisEquiv_chartComparison (s : ℂ ≃ₐ[ℚ] ℂ)
    (i : K →+* ℂ) (x : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) :
    C.embeddingMatrixGaloisEquiv hΦ b s x ((s : ℂ →+* ℂ).comp i) =
      C.embeddingChartComparison hΦ b s i (s.toRingEquiv.mapMatrix (x i)) := by
  rw [embeddingChartComparison_map, embeddingFactorGaloisEquiv_apply,
    embeddingFactorGaloisHom_apply]

end HarrisSignatureCharts
end Langlands.Shimura
