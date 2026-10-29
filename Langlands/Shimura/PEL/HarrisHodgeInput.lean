import Langlands.Shimura.PEL.RationalHodgeTwistProof
import Langlands.Shimura.PEL.KottwitzRegular

/-! # Actual positive Harris PEL input with the fixed Kottwitz Hodge sign -/

noncomputable section

universe u v w z

open scoped TensorProduct

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra

variable {E : Type u} {K : Type v} {A : Type w}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ} {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (D : CentralSimpleUnitaryData E K A n)
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- Select one unit from the proved simultaneous auxiliary and Hodge positivity. -/
def harrisHodgePELUnit : Aˣ :=
  (D.rationalHodgePolarizingTwistExists C).choose

theorem harrisHodgePELUnit_skew :
    D.involution (D.harrisHodgePELUnit C : A) =
      -(D.harrisHodgePELUnit C : A) :=
  (D.rationalHodgePolarizingTwistExists C).choose_spec.choose

/-- The auxiliary algebra with positive left involution, using that same unit. -/
def harrisHodgePELAlgebra : CentralSimpleUnitaryData E K A n :=
  D.skewTwist (D.harrisHodgePELUnit C) (D.harrisHodgePELUnit_skew C)

theorem harrisHodgePELAlgebra_isPositive :
    ((D.harrisHodgePELAlgebra C).toSecondKindInvolution.rationalInvolution.baseChange
      ℝ).IsPositive :=
  (D.rationalHodgePolarizingTwistExists C).choose_spec.choose_spec.1

theorem harrisHodgePEL_inverse_skew :
    (D.harrisHodgePELAlgebra C).involution (↑(D.harrisHodgePELUnit C)⁻¹ : A) =
      -(↑(D.harrisHodgePELUnit C)⁻¹ : A) :=
  D.involution.skewAdjoint_inverse_skew _ (D.harrisHodgePELUnit_skew C)

/-- The constructed normalized alternating form on the rational regular module. -/
def harrisHodgePELForm : LinearMap.BilinForm ℚ A :=
  (D.harrisHodgePELAlgebra C).tracePairing (D.harrisHodgePELUnit C)⁻¹

theorem harrisHodgePELForm_isAlt : (D.harrisHodgePELForm C).IsAlt :=
  (D.harrisHodgePELAlgebra C).tracePairing_isAlt _ (D.harrisHodgePEL_inverse_skew C)

theorem harrisHodgePELForm_nondegenerate : (D.harrisHodgePELForm C).Nondegenerate :=
  (D.harrisHodgePELAlgebra C).tracePairing_nondegenerate _

theorem harrisHodgePELForm_left (b x y : A) :
    D.harrisHodgePELForm C (b * x) y =
      D.harrisHodgePELForm C x ((D.harrisHodgePELAlgebra C).involution b * y) :=
  (D.harrisHodgePELAlgebra C).tracePairing_left _ b x y

/-- The right adjoint is the original Harris involution. -/
theorem harrisHodgePEL_rightAdjoint :
    (D.harrisHodgePELAlgebra C).tracePairingAdjoint (D.harrisHodgePELUnit C)⁻¹
      (D.harrisHodgePEL_inverse_skew C) =
        D.toSecondKindInvolution.rationalInvolution :=
  D.toSecondKindInvolution.rationalInvolution.skewAdjoint_inverse
    (D.harrisHodgePELUnit C) (D.harrisHodgePELUnit_skew C)

theorem harrisHodgePELForm_right (b x y : A) :
    D.harrisHodgePELForm C (x * b) y =
      D.harrisHodgePELForm C x (y * D.involution b) := by
  simpa only [harrisHodgePELForm, D.harrisHodgePEL_rightAdjoint C,
    SecondKindInvolution.rationalInvolution_apply] using
    (D.harrisHodgePELAlgebra C).tracePairing_right (D.harrisHodgePELUnit C)⁻¹
      (D.harrisHodgePEL_inverse_skew C) b x y

/-- The same rational form extended to an arbitrary commutative rational algebra. -/
def harrisHodgePELFormBaseChange (S : Type z) [CommRing S] [Algebra ℚ S] :
    LinearMap.BilinForm S (S ⊗[ℚ] A) :=
  (D.harrisHodgePELForm C).baseChange S

theorem harrisHodgePELFormBaseChange_eq (S : Type z) [CommRing S] [Algebra ℚ S] :
    D.harrisHodgePELFormBaseChange C S =
      (D.harrisHodgePELAlgebra C).tracePairingBaseChange S (D.harrisHodgePELUnit C)⁻¹ :=
  rfl

@[simp] theorem harrisHodgePELFormBaseChange_tmul
    (S : Type z) [CommRing S] [Algebra ℚ S] (s t : S) (x y : A) :
    D.harrisHodgePELFormBaseChange C S (s ⊗ₜ[ℚ] x) (t ⊗ₜ[ℚ] y) =
      algebraMap ℚ S (D.harrisHodgePELForm C x y) * (s * t) :=
  (D.harrisHodgePELAlgebra C).tracePairingBaseChange_tmul S _ s t x y

theorem harrisHodgePELFormBaseChange_isAlt
    (S : Type z) [CommRing S] [Algebra ℚ S] :
    (D.harrisHodgePELFormBaseChange C S).IsAlt :=
  (D.harrisHodgePELAlgebra C).tracePairingBaseChange_isAlt
    S _ (D.harrisHodgePEL_inverse_skew C)

theorem harrisHodgePELFormBaseChange_nondegenerate
    (S : Type z) [CommRing S] [Algebra ℚ S] :
    (D.harrisHodgePELFormBaseChange C S).Nondegenerate :=
  (D.harrisHodgePELAlgebra C).tracePairingBaseChange_nondegenerate S _

theorem harrisHodgePELFormBaseChange_left
    (S : Type z) [CommRing S] [Algebra ℚ S] (b x y : S ⊗[ℚ] A) :
    D.harrisHodgePELFormBaseChange C S (b * x) y =
      D.harrisHodgePELFormBaseChange C S x
        ((D.harrisHodgePELAlgebra C).toSecondKindInvolution.rationalInvolution.baseChange
          S b * y) :=
  (D.harrisHodgePELAlgebra C).tracePairingBaseChange_left S _ b x y

theorem harrisHodgePELFormBaseChange_right
    (S : Type z) [CommRing S] [Algebra ℚ S] (b x y : S ⊗[ℚ] A) :
    D.harrisHodgePELFormBaseChange C S (x * b) y =
      D.harrisHodgePELFormBaseChange C S x
        (y * D.toSecondKindInvolution.rationalInvolution.baseChange S b) :=
  D.skewTwist_tracePairingBaseChange_right
    (D.harrisHodgePELUnit C) (D.harrisHodgePELUnit_skew C) S b x y

/-- The symmetric positive form is built from the fixed original Kottwitz action. -/
def harrisHodgePELPolarizationForm : LinearMap.BilinForm ℝ (ℝ ⊗[ℚ] A) :=
  D.kottwitzTraceHodgeForm (D.harrisHodgePELUnit C) (D.harrisHodgePELUnit_skew C) C

@[simp] theorem harrisHodgePELPolarizationForm_apply (x y : ℝ ⊗[ℚ] A) :
    D.harrisHodgePELPolarizationForm C x y =
      D.harrisHodgePELFormBaseChange C ℝ x (D.kottwitzPELHom C Complex.I y) :=
  rfl

theorem harrisHodgePELPolarizationForm_isSymm :
    (D.harrisHodgePELPolarizationForm C).IsSymm :=
  D.kottwitzTraceHodgeForm_isSymm _ _ C

theorem harrisHodgePELPolarizationForm_pos (x : ℝ ⊗[ℚ] A) (hx : x ≠ 0) :
    0 < D.harrisHodgePELPolarizationForm C x x :=
  (D.rationalHodgePolarizingTwistExists C).choose_spec.choose_spec.2.2 x hx

theorem harrisHodgePELHom_adjoint (t : ℂ) (x y : ℝ ⊗[ℚ] A) :
    D.harrisHodgePELFormBaseChange C ℝ (D.kottwitzPELHom C t x) y =
      D.harrisHodgePELFormBaseChange C ℝ x (D.kottwitzPELHom C (star t) y) :=
  D.kottwitzPELHom_adjoint C _ _ t x y

theorem harrisHodgePELHom_normSq (t : ℂ) (x y : ℝ ⊗[ℚ] A) :
    D.harrisHodgePELFormBaseChange C ℝ
        (D.kottwitzPELHom C t x) (D.kottwitzPELHom C t y) =
      Complex.normSq t * D.harrisHodgePELFormBaseChange C ℝ x y :=
  D.kottwitzPELHom_normSq C _ _ t x y

/-- The original rational Harris group acts through right multiplication. -/
def harrisHodgePELSimilitudesEquiv :
    D.toSecondKindInvolution.rationalInvolution.similitudesᵐᵒᵖ ≃*
      PEL.bilinearSimilitudes A (D.harrisHodgePELForm C) :=
  PEL.algebraicBilinearEquiv _ _ (D.harrisHodgePELForm_nondegenerate C)
    (D.harrisHodgePELForm_right C)

@[simp] theorem harrisHodgePELSimilitudesEquiv_apply
    (g : D.toSecondKindInvolution.rationalInvolution.similitudesᵐᵒᵖ) (x : A) :
    (D.harrisHodgePELSimilitudesEquiv C g).val.1 x = x * (g.unop.val.1 : A) :=
  rfl

@[simp] theorem harrisHodgePELSimilitudesEquiv_multiplier
    (g : D.toSecondKindInvolution.rationalInvolution.similitudesᵐᵒᵖ) :
    PEL.bilinearSimilitudes.multiplier (D.harrisHodgePELForm C)
      (D.harrisHodgePELSimilitudesEquiv C g) =
        D.toSecondKindInvolution.rationalInvolution.multiplier g.unop :=
  rfl

/-- Right multiplication realizes the same group over every rational algebra. -/
def harrisHodgePELBaseChangeSimilitudesEquiv
    (S : Type z) [CommRing S] [Algebra ℚ S] :
    (D.toSecondKindInvolution.rationalInvolution.Points S)ᵐᵒᵖ ≃*
      PEL.bilinearSimilitudes (S ⊗[ℚ] A) (D.harrisHodgePELFormBaseChange C S) :=
  D.harrisTraceSimilitudesEquiv S (D.harrisHodgePELUnit C) (D.harrisHodgePELUnit_skew C)

@[simp] theorem harrisHodgePELBaseChangeSimilitudesEquiv_apply
    (S : Type z) [CommRing S] [Algebra ℚ S]
    (g : (D.toSecondKindInvolution.rationalInvolution.Points S)ᵐᵒᵖ)
    (x : S ⊗[ℚ] A) :
    (D.harrisHodgePELBaseChangeSimilitudesEquiv C S g).val.1 x =
      x * (g.unop.val.1 : S ⊗[ℚ] A) :=
  rfl

@[simp] theorem harrisHodgePELBaseChangeSimilitudesEquiv_multiplier
    (S : Type z) [CommRing S] [Algebra ℚ S]
    (g : (D.toSecondKindInvolution.rationalInvolution.Points S)ᵐᵒᵖ) :
    PEL.bilinearSimilitudes.multiplier (D.harrisHodgePELFormBaseChange C S)
      (D.harrisHodgePELBaseChangeSimilitudesEquiv C S g) =
        AlgebraInvolution.Points.multiplier
          D.toSecondKindInvolution.rationalInvolution S g.unop :=
  rfl

theorem harrisHodgePELHom_units_comparison (t : ℂˣ) :
    (D.harrisHodgePELBaseChangeSimilitudesEquiv C ℝ
      (MulOpposite.op ((D.realPositiveKottwitzHom C).val.toSimilitudes t))).val.1.toLinearMap =
        D.kottwitzPELHom C (t : ℂ) :=
  rfl

end Langlands.Shimura.CentralSimpleUnitaryData
