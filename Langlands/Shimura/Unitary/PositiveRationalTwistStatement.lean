import Langlands.Shimura.PEL.TracePairing

/-! # A rational positive skew-twist existence target -/

noncomputable section

universe u v w

open NumberField _root_.Algebra

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E : Type u} {K : Type v} {A : Type w}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ} {Φ : (E →+* ℝ) → (K →+* ℂ)}

/-- A rational skew unit whose conjugated involution is positive on the actual
real scalar extension of the Harris algebra. -/
def PositiveRationalSkewTwistExists (D : CentralSimpleUnitaryData E K A n)
    (_C : HarrisSignatureCharts D.toSecondKindInvolution n Φ) : Prop :=
  ∃ β : Aˣ, ∃ hβ : D.involution (β : A) = -(β : A),
    ((D.tracePairingAdjoint β hβ).baseChange ℝ).IsPositive

end Langlands.Shimura.CentralSimpleUnitaryData
