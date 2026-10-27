import Langlands.Shimura.PEL.PositiveInput
import Langlands.Shimura.Unitary.PositiveRationalTwistProof

/-! # Positive algebraic PEL input from the Harris signature charts -/

noncomputable section

universe u v w

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra

variable {E : Type u} {K : Type v} {A : Type w}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ} {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (D : CentralSimpleUnitaryData E K A n)
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- The rational skew unit supplied by the proved positive-twist theorem. -/
def harrisPositivePELUnit : Aˣ :=
  D.positivePELUnit C (D.positiveRationalSkewTwistExists C)

theorem harrisPositivePELUnit_skew :
    D.involution (D.harrisPositivePELUnit C : A) =
      -(D.harrisPositivePELUnit C : A) :=
  D.positivePELUnit_skew C (D.positiveRationalSkewTwistExists C)

/-- The auxiliary positive algebra is constructed from the Harris data and charts. -/
def harrisPositivePELAlgebra : CentralSimpleUnitaryData E K A n :=
  D.positivePELAlgebra C (D.positiveRationalSkewTwistExists C)

theorem harrisPositivePELAlgebra_isPositive :
    ((D.harrisPositivePELAlgebra C).toSecondKindInvolution.rationalInvolution.baseChange
      ℝ).IsPositive :=
  D.positivePELAlgebra_isPositive C (D.positiveRationalSkewTwistExists C)

theorem harrisPositivePEL_inverse_skew :
    (D.harrisPositivePELAlgebra C).involution (↑(D.harrisPositivePELUnit C)⁻¹ : A) =
      -(↑(D.harrisPositivePELUnit C)⁻¹ : A) :=
  D.positivePEL_inverse_skew C (D.positiveRationalSkewTwistExists C)

/-- The alternating nondegenerate rational trace form for the auxiliary algebra. -/
def harrisPositivePELForm : LinearMap.BilinForm ℚ A :=
  D.positivePELForm C (D.positiveRationalSkewTwistExists C)

variable [IsScalarTower E K A]

theorem harrisPositivePELForm_isAlt : (D.harrisPositivePELForm C).IsAlt :=
  D.positivePELForm_isAlt C (D.positiveRationalSkewTwistExists C)

theorem harrisPositivePELForm_nondegenerate :
    (D.harrisPositivePELForm C).Nondegenerate :=
  D.positivePELForm_nondegenerate C (D.positiveRationalSkewTwistExists C)

omit [IsScalarTower E K A] in
theorem harrisPositivePEL_rightAdjoint :
    (D.harrisPositivePELAlgebra C).tracePairingAdjoint (D.harrisPositivePELUnit C)⁻¹
      (D.harrisPositivePEL_inverse_skew C) =
        D.toSecondKindInvolution.rationalInvolution :=
  D.positivePEL_rightAdjoint C (D.positiveRationalSkewTwistExists C)

omit [IsScalarTower E K A] in
theorem harrisPositivePELForm_right (b x y : A) :
    D.harrisPositivePELForm C (x * b) y =
      D.harrisPositivePELForm C x (y * D.involution b) :=
  D.positivePELForm_right C (D.positiveRationalSkewTwistExists C) b x y

/-- Right multiplication identifies the opposite original Harris rational group
with the algebra-linear similitudes of the constructed form. -/
def harrisPositivePELSimilitudesEquiv :
    D.toSecondKindInvolution.rationalInvolution.similitudesᵐᵒᵖ ≃*
      PEL.bilinearSimilitudes A (D.harrisPositivePELForm C) :=
  D.positivePELSimilitudesEquiv C (D.positiveRationalSkewTwistExists C)

@[simp] theorem harrisPositivePELSimilitudesEquiv_apply
    (g : D.toSecondKindInvolution.rationalInvolution.similitudesᵐᵒᵖ) (x : A) :
    (D.harrisPositivePELSimilitudesEquiv C g).val.1 x = x * (g.unop.val.1 : A) := rfl

@[simp] theorem harrisPositivePELSimilitudesEquiv_multiplier
    (g : D.toSecondKindInvolution.rationalInvolution.similitudesᵐᵒᵖ) :
    PEL.bilinearSimilitudes.multiplier (D.harrisPositivePELForm C)
      (D.harrisPositivePELSimilitudesEquiv C g) =
        D.toSecondKindInvolution.rationalInvolution.multiplier g.unop := rfl

end Langlands.Shimura.CentralSimpleUnitaryData
