import Langlands.Shimura.Unitary.ComplexCocharacterConjugacy
import Langlands.Shimura.Unitary.GaloisCocharacters

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

/-- The actual first-factor Kottwitz cocharacter has precisely the Hodge-function stabilizer. -/
def ComplexCocharacterReflexStabilizer : Prop :=
  IsCMSection E K Φ → ∀ s : ℂ ≃ₐ[ℚ] ℂ,
    D.ComplexCocharacterConjugate
      (D.galoisCocharacter s (D.kottwitzCocharacter C true))
      (D.kottwitzCocharacter C true) ↔
        s ∈ hodgeStabilizer (D.realHodgeFunction C)

end Langlands.Shimura.CentralSimpleUnitaryData
