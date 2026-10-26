import Langlands.Shimura.Unitary.GaloisWeightRanksStatement
import Langlands.Shimura.Unitary.GaloisChartConjugators
import Langlands.Shimura.Unitary.SemilinearWeightSpaces

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj Classical

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (hΦ : IsCMSection E K Φ)

/-- Direct-model Galois transport preserves inverse-weight rank at the shifted embedding. -/
theorem finrank_directCocharacterWeightSpace_galois (s : ℂ ≃ₐ[ℚ] ℂ)
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
      D.rationalBaseChange rationalComplexBaseMap) (i : K →+* ℂ) :
    Module.finrank ℂ (D.directCocharacterWeightSpace C hΦ
      (GroupScheme.transportCocharacter rationalComplexBaseMap (complexGaloisBaseMap s)
        (complexGaloisBaseMap_over s) D.rationalGroupScheme χ)
      ((s : ℂ →+* ℂ).comp i)) =
        Module.finrank ℂ (D.directCocharacterWeightSpace C hΦ χ i) := by
  let a : ℂˣ → Matrix (Fin n) (Fin n) ℂ :=
    fun u => D.complexEmbeddingPointMatrices C hΦ (D.directComplexCocharacterValue χ u) i
  let U := C.embeddingChartConjugator hΦ D.totallyRealBasis s i
  have hf :
      (fun u => D.complexEmbeddingPointMatrices C hΦ
        (D.directComplexCocharacterValue
          (GroupScheme.transportCocharacter rationalComplexBaseMap (complexGaloisBaseMap s)
            (complexGaloisBaseMap_over s) D.rationalGroupScheme χ) u)
        ((s : ℂ →+* ℂ).comp i)) =
      (fun u => (U : Matrix (Fin n) (Fin n) ℂ) *
        ComplexMatrix.coefficientWeightFamily s.toRingEquiv a u *
        (↑(U⁻¹) : Matrix (Fin n) (Fin n) ℂ)) := by
    funext u
    exact (D.directComplexCocharacterValue_galois_matrices C hΦ s χ u i).trans
      (C.embeddingChartComparison_conj hΦ D.totallyRealBasis s i _)
  unfold directCocharacterWeightSpace complexEmbeddingWeightSpace
  rw [hf]
  exact (ComplexMatrix.finrank_inverseWeightSpace_conj
    (ComplexMatrix.coefficientWeightFamily s.toRingEquiv a) U).trans
    (ComplexMatrix.finrank_inverseWeightSpace_coefficient s.toRingEquiv a)

/-- The canonical direct-model comparison gives the same rank formula in the iterated model. -/
theorem finrank_complexCocharacterWeightSpace_galois (s : ℂ ≃ₐ[ℚ] ℂ)
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
      D.complexRationalGroupScheme) (i : K →+* ℂ) :
    Module.finrank ℂ (D.complexCocharacterWeightSpace C hΦ
      (D.galoisCocharacter s χ) ((s : ℂ →+* ℂ).comp i)) =
        Module.finrank ℂ (D.complexCocharacterWeightSpace C hΦ χ i) := by
  rw [D.complexCocharacterWeightSpace_comparison,
    D.galoisCocharacter_comparison, D.complexCocharacterWeightSpace_comparison]
  exact D.finrank_directCocharacterWeightSpace_galois C hΦ s
    (χ ≫ D.complexDirectGroupSchemeIso.hom) i

/-- The transported first-factor Kottwitz cocharacter has the original embedding Hodge rank. -/
theorem finrank_complexCocharacterWeightSpace_galois_kottwitz
    (s : ℂ ≃ₐ[ℚ] ℂ) (i : K →+* ℂ) :
    Module.finrank ℂ (D.complexCocharacterWeightSpace C hΦ
      (D.galoisCocharacter s (D.kottwitzCocharacter C true))
      ((s : ℂ →+* ℂ).comp i)) = D.realHodgeFunction C i :=
  (D.finrank_complexCocharacterWeightSpace_galois C hΦ s
    (D.kottwitzCocharacter C true) i).trans
    (D.finrank_complexCocharacterWeightSpace_kottwitz C hΦ i)

/-- Galois transport of actual cocharacters preserves all three stated weight-rank formulas. -/
theorem complexCocharacterGaloisWeightRanks : D.ComplexCocharacterGaloisWeightRanks C hΦ :=
  ⟨D.finrank_directCocharacterWeightSpace_galois C hΦ,
    D.finrank_complexCocharacterWeightSpace_galois C hΦ,
    D.finrank_complexCocharacterWeightSpace_galois_kottwitz C hΦ⟩

end Langlands.Shimura.CentralSimpleUnitaryData
