import Langlands.Shimura.Unitary.GaloisChartComparison
import Langlands.Algebra.MatrixAlgEquivInnerProof

noncomputable section
open NumberField Module Algebra
open scoped TensorProduct Classical

namespace Langlands.Shimura.HarrisSignatureCharts

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

/-- A matrix unit implementing the complex-linear comparison of Galois-shifted charts. -/
def embeddingChartConjugator (s : ℂ ≃ₐ[ℚ] ℂ) (i : K →+* ℂ) :
    (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  Classical.choose (Langlands.MatrixAlgebra.exists_unit_conj_of_algEquiv
    (C.embeddingChartComparison hΦ b s i))

/-- The chosen unit implements the chart comparison on every matrix. -/
theorem embeddingChartComparison_conj (s : ℂ ≃ₐ[ℚ] ℂ) (i : K →+* ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    C.embeddingChartComparison hΦ b s i M =
      (C.embeddingChartConjugator hΦ b s i : Matrix (Fin n) (Fin n) ℂ) * M *
        (↑((C.embeddingChartConjugator hΦ b s i)⁻¹) : Matrix (Fin n) (Fin n) ℂ) :=
  Classical.choose_spec (Langlands.MatrixAlgebra.exists_unit_conj_of_algEquiv
    (C.embeddingChartComparison hΦ b s i)) M

/-- Factor transport is conjugation after entrywise application of the coefficient action. -/
theorem embeddingFactorGaloisEquiv_conj (s : ℂ ≃ₐ[ℚ] ℂ) (i : K →+* ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    C.embeddingFactorGaloisEquiv hΦ b s i M =
      (C.embeddingChartConjugator hΦ b s i : Matrix (Fin n) (Fin n) ℂ) *
        s.toRingEquiv.mapMatrix M *
        (↑((C.embeddingChartConjugator hΦ b s i)⁻¹) : Matrix (Fin n) (Fin n) ℂ) :=
  (C.embeddingChartComparison_map hΦ b s i M).symm.trans
    (C.embeddingChartComparison_conj hΦ b s i (s.toRingEquiv.mapMatrix M))

/-- The full transported matrix array has the same conjugation formula at the shifted embedding. -/
theorem embeddingMatrixGaloisEquiv_conj (s : ℂ ≃ₐ[ℚ] ℂ) (i : K →+* ℂ)
    (x : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) :
    C.embeddingMatrixGaloisEquiv hΦ b s x ((s : ℂ →+* ℂ).comp i) =
      (C.embeddingChartConjugator hΦ b s i : Matrix (Fin n) (Fin n) ℂ) *
        s.toRingEquiv.mapMatrix (x i) *
        (↑((C.embeddingChartConjugator hΦ b s i)⁻¹) : Matrix (Fin n) (Fin n) ℂ) :=
  (C.embeddingMatrixGaloisEquiv_chartComparison hΦ b s i x).trans
    (C.embeddingChartComparison_conj hΦ b s i (s.toRingEquiv.mapMatrix (x i)))

end Langlands.Shimura.HarrisSignatureCharts
