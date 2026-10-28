import Langlands.Shimura.PEL.TracePairingBaseChange
import Langlands.Shimura.Unitary.RealPositivity

/-! # A rational skew twist with the Kottwitz Hodge sign -/

noncomputable section

universe u v w

open NumberField _root_.Algebra
open scoped TensorProduct

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E : Type u} {K : Type v} {A : Type w}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ} {Φ : (E →+* ℝ) → (K →+* ℂ)}

/-- A rational skew unit with positive auxiliary involution whose actual
inverse-unit trace form polarizes the constructed Kottwitz homomorphism. -/
def RationalHodgePolarizingTwistExists (D : CentralSimpleUnitaryData E K A n)
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ) : Prop :=
  let J := (D.realPositiveKottwitzHom C).val.hom Complex.I
  ∃ β : Aˣ, ∃ hβ : D.involution (β : A) = -(β : A),
    ((D.skewTwist β hβ).toSecondKindInvolution.rationalInvolution.baseChange
      ℝ).IsPositive ∧
    (let ψ := (D.skewTwist β hβ).tracePairingBaseChange ℝ β⁻¹
     (∀ x y : ℝ ⊗[ℚ] A, ψ x (y * J) = ψ y (x * J)) ∧
       ∀ x : ℝ ⊗[ℚ] A, x ≠ 0 → 0 < ψ x (x * J))

end Langlands.Shimura.CentralSimpleUnitaryData
