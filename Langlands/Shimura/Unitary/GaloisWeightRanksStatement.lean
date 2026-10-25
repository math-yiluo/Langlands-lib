import Langlands.Shimura.Unitary.CocharacterEmbeddingWeights

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (hΦ : IsCMSection E K Φ)

/-- Galois transport preserves the embedding-labelled inverse-weight ranks of actual
scheme cocharacters, and transports the Kottwitz ranks from the real Hodge function. -/
def ComplexCocharacterGaloisWeightRanks : Prop :=
  (∀ (s : ℂ ≃ₐ[ℚ] ℂ)
      (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
        D.rationalBaseChange rationalComplexBaseMap) (i : K →+* ℂ),
    Module.finrank ℂ (D.directCocharacterWeightSpace C hΦ
      (GroupScheme.transportCocharacter rationalComplexBaseMap (complexGaloisBaseMap s)
        (complexGaloisBaseMap_over s) D.rationalGroupScheme χ)
      ((s : ℂ →+* ℂ).comp i)) =
        Module.finrank ℂ (D.directCocharacterWeightSpace C hΦ χ i)) ∧
  (∀ (s : ℂ ≃ₐ[ℚ] ℂ)
      (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
        D.complexRationalGroupScheme) (i : K →+* ℂ),
    Module.finrank ℂ (D.complexCocharacterWeightSpace C hΦ
      (D.galoisCocharacter s χ) ((s : ℂ →+* ℂ).comp i)) =
        Module.finrank ℂ (D.complexCocharacterWeightSpace C hΦ χ i)) ∧
  (∀ (s : ℂ ≃ₐ[ℚ] ℂ) (i : K →+* ℂ),
    Module.finrank ℂ (D.complexCocharacterWeightSpace C hΦ
      (D.galoisCocharacter s (D.kottwitzCocharacter C true))
      ((s : ℂ →+* ℂ).comp i)) = D.realHodgeFunction C i)

end Langlands.Shimura.CentralSimpleUnitaryData
