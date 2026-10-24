import Langlands.Shimura.Unitary.GaloisChartComparison
import Langlands.Shimura.Unitary.GaloisCocharacterPoints

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (hΦ : IsCMSection E K Φ)

/-- Embedding-labelled matrix coordinates of actual complex points of the rational group. -/
def complexEmbeddingPointMatrices :
    ((algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶
      D.rationalGroupScheme.X) →* ((K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) :=
  (C.embeddingMatrixEquiv hΦ D.totallyRealBasis).toMonoidHom.comp
    ((Units.coeHom (ℂ ⊗[ℚ] A)).comp
      ((D.toSecondKindInvolution.rationalInvolution.baseChange ℂ).underlyingUnit.comp
        (D.rationalAffinePointsEquiv (CommAlgCat.of ℚ ℂ)).toMonoidHom))

/-- The common multiplier of an actual rational-group complex point. -/
def complexPointMultiplier :
    ((algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶
      D.rationalGroupScheme.X) →* ℂˣ :=
  (D.toSecondKindInvolution.rationalInvolution.baseChange ℂ).multiplier.comp
    (D.rationalAffinePointsEquiv (CommAlgCat.of ℚ ℂ)).toMonoidHom

/-- Matrix coordinates together with the retained similitude multiplier. -/
def complexEmbeddingPointCoordinates :
    ((algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶
      D.rationalGroupScheme.X) →*
        (((K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) × ℂˣ) :=
  (D.complexEmbeddingPointMatrices C hΦ).prod D.complexPointMultiplier

/-- The matrix array and multiplier determine the original scheme point. -/
theorem complexEmbeddingPointCoordinates_injective :
    Function.Injective (D.complexEmbeddingPointCoordinates C hΦ) := by
  intro x y h
  apply (D.rationalAffinePointsEquiv (CommAlgCat.of ℚ ℂ)).injective
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    apply (C.embeddingMatrixEquiv hΦ D.totallyRealBasis).injective
    exact congrArg Prod.fst h
  · have hm := congrArg
      (fun p : ((K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) × ℂˣ => p.2) h
    exact hm

set_option maxRecDepth 2048 in
/-- The actual scheme-point action agrees with the full matrix coefficient action. -/
theorem complexEmbeddingPointMatrices_galois (s : ℂ ≃ₐ[ℚ] ℂ)
    (x : (algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶
      D.rationalGroupScheme.X) :
    D.complexEmbeddingPointMatrices C hΦ (D.complexPointGaloisAction s x) =
      C.embeddingMatrixGaloisEquiv hΦ D.totallyRealBasis s
        (D.complexEmbeddingPointMatrices C hΦ x) := by
  change C.embeddingMatrixEquiv hΦ D.totallyRealBasis
    ((D.rationalAffinePointsEquiv (CommAlgCat.of ℚ ℂ)
      (D.complexPointGaloisAction s x)).val.1 : ℂ ⊗[ℚ] A) =
    C.embeddingMatrixGaloisEquiv hΦ D.totallyRealBasis s
      (C.embeddingMatrixEquiv hΦ D.totallyRealBasis
        ((D.rationalAffinePointsEquiv (CommAlgCat.of ℚ ℂ) x).val.1 : ℂ ⊗[ℚ] A))
  rw [D.complexPointGaloisAction_coordinates, AlgebraInvolution.coefficientAut_underlying,
    ← ComplexMatrix.coefficientEquiv_eq_changeCoefficients,
    C.embeddingMatrixGaloisEquiv_apply]

/-- Galois moves each actual point matrix from i to s composed with i, with the chart comparison. -/
theorem complexEmbeddingPointMatrices_galois_factor (s : ℂ ≃ₐ[ℚ] ℂ)
    (x : (algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶
      D.rationalGroupScheme.X) (i : K →+* ℂ) :
    D.complexEmbeddingPointMatrices C hΦ (D.complexPointGaloisAction s x)
        ((s : ℂ →+* ℂ).comp i) =
      C.embeddingChartComparison hΦ D.totallyRealBasis s i
        (s.toRingEquiv.mapMatrix (D.complexEmbeddingPointMatrices C hΦ x i)) := by
  rw [D.complexEmbeddingPointMatrices_galois,
    C.embeddingMatrixGaloisEquiv_chartComparison]

omit [IsScalarTower E K A] in
/-- The same coefficient automorphism acts on the common multiplier. -/
theorem complexPointMultiplier_galois (s : ℂ ≃ₐ[ℚ] ℂ)
    (x : (algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶
      D.rationalGroupScheme.X) :
    D.complexPointMultiplier (D.complexPointGaloisAction s x) =
      Units.map s.toMonoidHom (D.complexPointMultiplier x) := by
  change (D.toSecondKindInvolution.rationalInvolution.baseChange ℂ).multiplier
    (D.rationalAffinePointsEquiv (CommAlgCat.of ℚ ℂ)
      (D.complexPointGaloisAction s x)) = _
  rw [D.complexPointGaloisAction_coordinates,
    AlgebraInvolution.coefficientAut_multiplier]
  rfl

/-- Direct-model cocharacter transport has the actual factorwise matrix formula. -/
theorem directComplexCocharacterValue_galois_matrices (s : ℂ ≃ₐ[ℚ] ℂ)
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
      D.rationalBaseChange rationalComplexBaseMap) (u : ℂˣ) (i : K →+* ℂ) :
    D.complexEmbeddingPointMatrices C hΦ
        (D.directComplexCocharacterValue
          (GroupScheme.transportCocharacter rationalComplexBaseMap (complexGaloisBaseMap s)
            (complexGaloisBaseMap_over s) D.rationalGroupScheme χ) u)
        ((s : ℂ →+* ℂ).comp i) =
      C.embeddingChartComparison hΦ D.totallyRealBasis s i
        (s.toRingEquiv.mapMatrix
          (D.complexEmbeddingPointMatrices C hΦ
            (D.directComplexCocharacterValue χ (Units.map s.symm.toMonoidHom u)) i)) := by
  rw [D.directComplexCocharacterValue_transport,
    D.complexEmbeddingPointMatrices_galois_factor]

end Langlands.Shimura.CentralSimpleUnitaryData
