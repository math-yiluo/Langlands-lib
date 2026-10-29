import Langlands.Shimura.PEL.HodgeDeterminant
import Langlands.Shimura.PEL.HarrisIntegralOrder
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-! # Integral coefficients of the actual Harris order Hodge determinant -/

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

/-- Every coefficient for a family in the constructed Harris integer order is
an algebraic integer in the complex coefficient field. -/
def KottwitzIntegralHodgeDeterminantCoefficients : Prop :=
  IsCMSection E K Φ →
    ∀ (ι : Type) [Fintype ι] (a : ι → D.harrisHodgePELIntegralOrder C)
      (d : ι →₀ ℕ),
      IsIntegral ℤ
        ((D.kottwitzHodgeDeterminant C (fun i => (a i : A))).coeff d)

end Langlands.Shimura.CentralSimpleUnitaryData
