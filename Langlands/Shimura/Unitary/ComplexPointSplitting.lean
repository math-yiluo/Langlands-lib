import Langlands.Shimura.Unitary.ComplexAffineKottwitz
import Langlands.Shimura.Unitary.ComplexGroupSplitting

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra Matrix
open scoped CategoryTheory.MonObj Classical TensorProduct

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (hΦ : IsCMSection E K Φ)

/-- Split the actual complex points of the rational Harris model into matrices and multiplier. -/
def complexRationalPointSplitting :
    ((algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶
      D.rationalGroupScheme.X) ≃*
        (((E →+* ℝ) → (Matrix (Fin n) (Fin n) ℂ)ˣ) × ℂˣ) :=
  (D.rationalAffinePointsEquiv (CommAlgCat.of ℚ ℂ)).trans
    (C.scalarGroupSplitting D.totallyRealBasis ℂ)

/-- The scalar coordinate is the existing rational-model multiplier. -/
theorem complexRationalPointSplitting_multiplier
    (x : (algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶
      D.rationalGroupScheme.X) :
    (D.complexRationalPointSplitting C x).2 = D.complexPointMultiplier x := by
  exact Units.ext rfl

/-- The selected matrix is exactly the coordinate at the corresponding chosen CM embedding. -/
theorem complexRationalPointSplitting_matrix
    (x : (algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶
      D.rationalGroupScheme.X) (τ : E →+* ℝ) :
    ((D.complexRationalPointSplitting C x).1 τ : Matrix (Fin n) (Fin n) ℂ) =
      D.complexEmbeddingPointMatrices C hΦ x (Φ τ) := by
  change (C.scalarMatrixEquiv D.totallyRealBasis ℂ
    ((D.rationalAffinePointsEquiv (CommAlgCat.of ℚ ℂ) x).val.1 : ℂ ⊗[ℚ] A) τ).1 =
      C.embeddingMatrixEquiv hΦ D.totallyRealBasis
        ((D.rationalAffinePointsEquiv (CommAlgCat.of ℚ ℂ) x).val.1 : ℂ ⊗[ℚ] A) (Φ τ)
  rw [show Φ τ = cmFactorEmbedding Φ (τ, true) from rfl,
    C.embeddingMatrixEquiv_factor]
  simp only [HarrisSignatureCharts.scalarMatrixEquiv, HarrisSignatureCharts.complexMatrixEquiv,
    AlgEquiv.trans_apply, C.iteratedScalarMatrixEquiv_complex, ↓reduceIte]

/-- Selected embedding matrices and the common multiplier determine the whole actual point. -/
theorem complexRationalPoint_ext
    {x y : (algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶
      D.rationalGroupScheme.X}
    (hm : ∀ τ, D.complexEmbeddingPointMatrices C hΦ x (Φ τ) =
      D.complexEmbeddingPointMatrices C hΦ y (Φ τ))
    (hc : D.complexPointMultiplier x = D.complexPointMultiplier y) : x = y := by
  apply (D.complexRationalPointSplitting C).injective
  apply Prod.ext
  · funext τ
    apply Units.ext
    simpa only [D.complexRationalPointSplitting_matrix C hΦ] using hm τ
  · simpa only [D.complexRationalPointSplitting_multiplier] using hc

/-- Lift an arbitrary family of invertible matrices to one actual multiplier-one Harris point. -/
def complexMatrixPoint (m : (E →+* ℝ) → (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    (algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶
      D.rationalGroupScheme.X :=
  (D.complexRationalPointSplitting C).symm (m, 1)

/-- The lifted point has exactly the prescribed matrices at all selected CM embeddings. -/
theorem complexMatrixPoint_matrices
    (m : (E →+* ℝ) → (Matrix (Fin n) (Fin n) ℂ)ˣ) (τ : E →+* ℝ) :
    D.complexEmbeddingPointMatrices C hΦ (D.complexMatrixPoint C m) (Φ τ) =
      (m τ : Matrix (Fin n) (Fin n) ℂ) := by
  rw [← D.complexRationalPointSplitting_matrix C hΦ]
  change (((D.complexRationalPointSplitting C)
    ((D.complexRationalPointSplitting C).symm (m, 1))).1 τ : Matrix (Fin n) (Fin n) ℂ) = _
  rw [MulEquiv.apply_symm_apply]

/-- The lifted point has common multiplier one. -/
theorem complexMatrixPoint_multiplier
    (m : (E →+* ℝ) → (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    D.complexPointMultiplier (D.complexMatrixPoint C m) = 1 := by
  rw [← D.complexRationalPointSplitting_multiplier C]
  exact congrArg Prod.snd ((D.complexRationalPointSplitting C).apply_symm_apply (m, 1))

end Langlands.Shimura.CentralSimpleUnitaryData
