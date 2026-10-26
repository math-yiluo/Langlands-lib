import Langlands.Shimura.Unitary.CocharacterReflexStatement
import Langlands.Shimura.Unitary.GaloisWeightRanksProof

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

include hΦ in
/-- Actual Galois conjugacy of the Kottwitz cocharacter forces preservation of the Hodge function. -/
theorem mem_hodgeStabilizer_of_galois_cocharacter_conjugate (s : ℂ ≃ₐ[ℚ] ℂ)
    (h : D.ComplexCocharacterConjugate
      (D.galoisCocharacter s (D.kottwitzCocharacter C true))
      (D.kottwitzCocharacter C true)) :
    s ∈ hodgeStabilizer (D.realHodgeFunction C) := by
  intro i
  calc
    D.realHodgeFunction C ((s : ℂ →+* ℂ).comp i) =
        Module.finrank ℂ (D.complexCocharacterWeightSpace C hΦ
          (D.kottwitzCocharacter C true) ((s : ℂ →+* ℂ).comp i)) :=
      (D.finrank_complexCocharacterWeightSpace_kottwitz C hΦ _).symm
    _ = Module.finrank ℂ (D.complexCocharacterWeightSpace C hΦ
          (D.galoisCocharacter s (D.kottwitzCocharacter C true))
          ((s : ℂ →+* ℂ).comp i)) :=
      (D.finrank_complexCocharacterWeightSpace_of_conjugate C hΦ h _).symm
    _ = D.realHodgeFunction C i :=
      D.finrank_complexCocharacterWeightSpace_galois_kottwitz C hΦ s i

end Langlands.Shimura.CentralSimpleUnitaryData
