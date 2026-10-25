import Langlands.Shimura.Unitary.ComplexGroupSchemeSplitting
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

noncomputable section
open AlgebraicGeometry Algebra

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)

/-- The actual rational Harris similitude group is smooth when signature charts are given. -/
def RationalGroupSchemeSmooth : Prop :=
  ∀ {Φ : (E →+* ℝ) → (K →+* ℂ)},
    HarrisSignatureCharts D.toSecondKindInvolution n Φ →
      Smooth D.rationalGroupScheme.X.hom

end Langlands.Shimura.CentralSimpleUnitaryData
