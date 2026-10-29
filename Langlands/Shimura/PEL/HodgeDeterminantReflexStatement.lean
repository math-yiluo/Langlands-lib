import Langlands.Shimura.PEL.HodgeDeterminant
import Langlands.Shimura.Unitary.CocharacterReflexField

/-! # Reflex-field coefficients of the actual regular Hodge determinant -/

noncomputable section

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra

variable {E K A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
    {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- Every coefficient of the constructed regular Hodge determinant lies in
the fixed field of the actual Kottwitz cocharacter class. -/
def KottwitzHodgeDeterminantReflexDescent : Prop :=
  IsCMSection E K Φ →
    ∀ (ι : Type) [Fintype ι] (a : ι → A) (d : ι →₀ ℕ),
      (D.kottwitzHodgeDeterminant C a).coeff d ∈
        D.kottwitzCocharacterReflexField C

end Langlands.Shimura.CentralSimpleUnitaryData
