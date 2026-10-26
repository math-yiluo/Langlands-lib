import Langlands.Shimura.Unitary.CocharacterFixedField
import Langlands.Shimura.Unitary.CocharacterReflexProof

noncomputable section

open NumberField Algebra

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- The actual Kottwitz cocharacter and real Hodge function have the same Galois subgroup. -/
theorem kottwitzCocharacterStabilizer_eq (hΦ : IsCMSection E K Φ) :
    D.complexCocharacterStabilizer (D.kottwitzCocharacter C true) =
      hodgeStabilizer (D.realHodgeFunction C) := by
  ext s
  exact D.complexCocharacterReflexStabilizer C hΦ s

/-- The field of the actual scheme-cocharacter class equals the real Hodge reflex field. -/
theorem kottwitzCocharacterReflexField_eq_realReflexField (hΦ : IsCMSection E K Φ) :
    D.kottwitzCocharacterReflexField C = D.realReflexField C := by
  change IntermediateField.fixedField
    (D.complexCocharacterStabilizer (D.kottwitzCocharacter C true)) =
      IntermediateField.fixedField (hodgeStabilizer (D.realHodgeFunction C))
  rw [D.kottwitzCocharacterStabilizer_eq C hΦ]

/-- The actual scheme-cocharacter field equals the calculated chart reflex field. -/
theorem kottwitzCocharacterReflexField_eq_reflexField (hΦ : IsCMSection E K Φ) :
    D.kottwitzCocharacterReflexField C = C.reflexField := by
  rw [D.kottwitzCocharacterReflexField_eq_realReflexField C hΦ, D.realReflexField_eq]

/-- In rank two with one real place, the actual cocharacter reflex field is rational. -/
theorem kottwitzCocharacterReflexField_eq_bot (hΦ : IsCMSection E K Φ)
    (h2 : n = 2) [Subsingleton (E →+* ℝ)] :
    D.kottwitzCocharacterReflexField C = ⊥ := by
  rw [D.kottwitzCocharacterReflexField_eq_realReflexField C hΦ]
  exact D.realReflexField_eq_bot C h2

/-- Construct the actual scheme-cocharacter fixed field from signature and CM-section data. -/
def kottwitzCocharacterReflexFieldOfSignature
    (h : HasHarrisSignature D.toSecondKindInvolution n)
    (hΦ : IsCMSection E K Φ) : IntermediateField ℚ ℂ :=
  D.kottwitzCocharacterReflexField (HarrisSignatureCharts.ofSignature h hΦ)

/-- The two signature-based constructions give the same intermediate field. -/
theorem kottwitzCocharacterReflexFieldOfSignature_eq
    (h : HasHarrisSignature D.toSecondKindInvolution n)
    (hΦ : IsCMSection E K Φ) :
    D.kottwitzCocharacterReflexFieldOfSignature h hΦ = D.realReflexFieldOfSignature h hΦ :=
  D.kottwitzCocharacterReflexField_eq_realReflexField
    (HarrisSignatureCharts.ofSignature h hΦ) hΦ

variable {F : Type} [Field F] [NumberField F] [IsCMField F] [IsQuadraticExtension ℚ F]
  {j : F →+* K} {τ₀ : F →+* ℂ}
  (CH : HarrisSignatureCharts D.toSecondKindInvolution n (harrisCMSection E j τ₀))

/-- In the nonexceptional Harris case, the actual cocharacter reflex field is the CM image. -/
theorem kottwitzCocharacterReflexField_eq_distinguishedImage
    (h : 3 ≤ n ∨ ∃ τ, τ ≠ CH.distinguished) :
    D.kottwitzCocharacterReflexField CH = CH.distinguishedImage := by
  rw [D.kottwitzCocharacterReflexField_eq_realReflexField CH
    (isCMSection_harrisCMSection E j τ₀)]
  exact D.realReflexField_eq_distinguishedImage CH h

end Langlands.Shimura.CentralSimpleUnitaryData
