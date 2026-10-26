import Langlands.Shimura.Unitary.PositiveRationalTwistStatement
import Langlands.Shimura.PEL.TraceSimilitudes

/-! # Positive PEL algebraic input retaining the original Harris group -/

noncomputable section

universe u v w

namespace Langlands.Shimura.AlgebraInvolution

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

theorem ext_of_apply_eq {σ τ : AlgebraInvolution R A} (h : ∀ a, σ a = τ a) : σ = τ := by
  cases σ
  cases τ
  congr 1
  exact LinearMap.ext h

theorem skewAdjoint_inverse_skew (σ : AlgebraInvolution R A) (β : Aˣ)
    (hβ : σ (β : A) = -(β : A)) :
    σ.skewAdjoint β hβ (↑β⁻¹ : A) = -(↑β⁻¹ : A) := by
  have hu : σ.units β = -β := Units.ext hβ
  have hi : σ (↑β⁻¹ : A) = -(↑β⁻¹ : A) := by
    change (σ.units β⁻¹ : A) = _
    rw [σ.units_inv, hu]
    simp
  simp [hi]

/-- Twisting by a skew unit and then its inverse recovers the original involution. -/
theorem skewAdjoint_inverse (σ : AlgebraInvolution R A) (β : Aˣ)
    (hβ : σ (β : A) = -(β : A)) :
    (σ.skewAdjoint β hβ).skewAdjoint β⁻¹ (σ.skewAdjoint_inverse_skew β hβ) = σ := by
  apply ext_of_apply_eq
  intro a
  simp [mul_assoc]

end Langlands.Shimura.AlgebraInvolution

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField Module _root_.Algebra

variable {E : Type u} {K : Type v} {A : Type w}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ}

/-- Change only the involution, using an actual skew unit. The center action
remains the specified CM conjugation. -/
def skewTwist (D : CentralSimpleUnitaryData E K A n) (β : Aˣ)
    (hβ : D.involution (β : A) = -(β : A)) : CentralSimpleUnitaryData E K A n where
  involution := D.involution.skewAdjoint β hβ
  onCenter k := by
    rw [AlgebraInvolution.skewAdjoint_apply, D.onCenter,
      ← Algebra.commutes (cmConjugation E K k) (β : A)]
    simp [mul_assoc]
  rank_gt_one := D.rank_gt_one
  central := D.central
  simple := D.simple
  finite := D.finite
  dimension := D.dimension

variable (D : CentralSimpleUnitaryData E K A n)

omit [IsScalarTower E K A] in
@[simp] theorem skewTwist_rationalInvolution (β : Aˣ)
    (hβ : D.involution (β : A) = -(β : A)) :
    (D.skewTwist β hβ).toSecondKindInvolution.rationalInvolution =
      D.tracePairingAdjoint β hβ := rfl

variable {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
    (h : D.PositiveRationalSkewTwistExists C)

/-- Select the unit from the specific rational positive-twist existence theorem. -/
def positivePELUnit : Aˣ := h.choose

omit [IsScalarTower E K A] in
theorem positivePELUnit_skew : D.involution (D.positivePELUnit C h : A) =
    -(D.positivePELUnit C h : A) := h.choose_spec.choose

/-- The actual auxiliary central simple CM algebra with positive left involution. -/
def positivePELAlgebra : CentralSimpleUnitaryData E K A n :=
  D.skewTwist (D.positivePELUnit C h) (D.positivePELUnit_skew C h)

omit [IsScalarTower E K A] in
theorem positivePELAlgebra_isPositive :
    ((D.positivePELAlgebra C h).toSecondKindInvolution.rationalInvolution.baseChange ℝ).IsPositive :=
  h.choose_spec.choose_spec

omit [IsScalarTower E K A] in
theorem positivePEL_inverse_skew :
    (D.positivePELAlgebra C h).involution (↑(D.positivePELUnit C h)⁻¹ : A) =
      -(↑(D.positivePELUnit C h)⁻¹ : A) :=
  D.involution.skewAdjoint_inverse_skew _ (D.positivePELUnit_skew C h)

/-- The actual alternating rational form for the positive auxiliary involution. -/
def positivePELForm : LinearMap.BilinForm ℚ A :=
  (D.positivePELAlgebra C h).tracePairing (D.positivePELUnit C h)⁻¹

theorem positivePELForm_isAlt : (D.positivePELForm C h).IsAlt :=
  (D.positivePELAlgebra C h).tracePairing_isAlt _ (D.positivePEL_inverse_skew C h)

theorem positivePELForm_nondegenerate : (D.positivePELForm C h).Nondegenerate :=
  (D.positivePELAlgebra C h).tracePairing_nondegenerate _

omit [IsScalarTower E K A] in
/-- The right adjoint of this form is the original Harris involution. -/
theorem positivePEL_rightAdjoint :
    (D.positivePELAlgebra C h).tracePairingAdjoint (D.positivePELUnit C h)⁻¹
      (D.positivePEL_inverse_skew C h) =
        D.toSecondKindInvolution.rationalInvolution :=
  D.toSecondKindInvolution.rationalInvolution.skewAdjoint_inverse
    (D.positivePELUnit C h) (D.positivePELUnit_skew C h)

omit [IsScalarTower E K A] in
theorem positivePELForm_right (b x y : A) :
    D.positivePELForm C h (x * b) y =
      D.positivePELForm C h x (y * D.involution b) := by
  simpa only [positivePELForm, D.positivePEL_rightAdjoint C h,
    SecondKindInvolution.rationalInvolution_apply] using
    (D.positivePELAlgebra C h).tracePairing_right (D.positivePELUnit C h)⁻¹
      (D.positivePEL_inverse_skew C h) b x y

/-- The original Harris rational group is recovered, with the right-multiplication
opposite convention and the same multiplier. -/
def positivePELSimilitudesEquiv :
    D.toSecondKindInvolution.rationalInvolution.similitudesᵐᵒᵖ ≃*
      PEL.bilinearSimilitudes A (D.positivePELForm C h) :=
  PEL.algebraicBilinearEquiv _ _ (D.positivePELForm_nondegenerate C h)
    (D.positivePELForm_right C h)

@[simp] theorem positivePELSimilitudesEquiv_apply
    (g : D.toSecondKindInvolution.rationalInvolution.similitudesᵐᵒᵖ) (x : A) :
    (D.positivePELSimilitudesEquiv C h g).val.1 x = x * (g.unop.val.1 : A) := rfl

@[simp] theorem positivePELSimilitudesEquiv_multiplier
    (g : D.toSecondKindInvolution.rationalInvolution.similitudesᵐᵒᵖ) :
    PEL.bilinearSimilitudes.multiplier (D.positivePELForm C h)
      (D.positivePELSimilitudesEquiv C h g) =
        D.toSecondKindInvolution.rationalInvolution.multiplier g.unop := rfl

end Langlands.Shimura.CentralSimpleUnitaryData
