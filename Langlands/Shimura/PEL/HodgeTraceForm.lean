import Langlands.Shimura.PEL.TracePairingBaseChange
import Langlands.Shimura.Unitary.RealPositivity

/-! # The actual trace Hodge form and its signed diagonal formula -/

noncomputable section

universe u v w z

open scoped TensorProduct

namespace Langlands.Shimura.AlgebraInvolution

variable {B : Type*} [Ring B] [Algebra ℝ B] {σ : AlgebraInvolution ℝ B}

/-- The real element h(-i) has the signed trace positivity required for the
Hodge form after substituting x = beta y. -/
theorem PositiveComplexHom.signed_trace_pos (h : PositiveComplexHom σ)
    (y : B) (hy : y ≠ 0) :
    0 < Langlands.Algebra.regularTrace ℝ B
      (h.val.hom (-Complex.I) * y * h.val.hom Complex.I * σ y) := by
  have hσy : σ y ≠ 0 := by
    intro h0
    apply hy
    have hh := congrArg σ h0
    simpa only [σ.apply_apply, σ.apply_zero] using hh
  have hp := h.property (σ y) hσy
  simpa only [Langlands.Algebra.regularTrace_apply, ComplexHom.twist_apply,
    σ.apply_apply] using hp

end Langlands.Shimura.AlgebraInvolution

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField Module _root_.Algebra

variable {E : Type u} {K : Type v} {A : Type w}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
    (β : Aˣ) (hβ : D.involution (β : A) = -(β : A))

omit [IsScalarTower E K A] in
/-- The extended inverse-unit form has the original involution as right adjoint. -/
theorem skewTwist_tracePairingBaseChange_right (S : Type z)
    [CommRing S] [Algebra ℚ S] (b x y : S ⊗[ℚ] A) :
    (D.skewTwist β hβ).tracePairingBaseChange S β⁻¹ (x * b) y =
      (D.skewTwist β hβ).tracePairingBaseChange S β⁻¹ x
        (y * D.toSecondKindInvolution.rationalInvolution.baseChange S b) := by
  rw [D.skewTwist_tracePairingBaseChange_apply,
    D.skewTwist_tracePairingBaseChange_apply]
  simp only [AlgebraInvolution.apply_mul, AlgebraInvolution.apply_apply, mul_assoc]

variable {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- The actual real Hodge form psi(x,y h0(i)), using the constructed Kottwitz h0. -/
def kottwitzTraceHodgeForm : LinearMap.BilinForm ℝ (ℝ ⊗[ℚ] A) :=
  ((D.skewTwist β hβ).tracePairingBaseChange ℝ β⁻¹).compRight
    (LinearMap.mulRight ℝ ((D.realPositiveKottwitzHom C).val.hom Complex.I))

@[simp] theorem kottwitzTraceHodgeForm_apply (x y : ℝ ⊗[ℚ] A) :
    D.kottwitzTraceHodgeForm β hβ C x y =
      (D.skewTwist β hβ).tracePairingBaseChange ℝ β⁻¹ x
        (y * (D.realPositiveKottwitzHom C).val.hom Complex.I) := rfl

/-- Symmetry is intrinsic for every rational skew unit, independently of its sign. -/
theorem kottwitzTraceHodgeForm_isSymm : (D.kottwitzTraceHodgeForm β hβ C).IsSymm := by
  let J := (D.realPositiveKottwitzHom C).val.hom Complex.I
  have hJ : D.toSecondKindInvolution.rationalInvolution.baseChange ℝ J = -J := by
    simpa only [J, Complex.star_def, Complex.conj_I, map_neg] using
      (D.realPositiveKottwitzHom C).val.star_compatible Complex.I
  have hγ : (D.skewTwist β hβ).involution (↑β⁻¹ : A) = -(↑β⁻¹ : A) :=
    D.involution.skewAdjoint_inverse_skew β hβ
  constructor
  intro x y
  change (D.skewTwist β hβ).tracePairingBaseChange ℝ β⁻¹ x (y * J) =
    (D.skewTwist β hβ).tracePairingBaseChange ℝ β⁻¹ y (x * J)
  have hr := D.skewTwist_tracePairingBaseChange_right β hβ ℝ J x y
  rw [hJ, mul_neg, map_neg] at hr
  have hs := (D.skewTwist β hβ).tracePairingBaseChange_skew ℝ β⁻¹ hγ (x * J) y
  rw [hr, neg_neg] at hs
  exact hs.symm

/-- Substituting x = (1 tensor beta)y removes the inverse unit from the Hodge diagonal. -/
theorem kottwitzTraceHodgeForm_diagonal_mul (y : ℝ ⊗[ℚ] A) :
    D.kottwitzTraceHodgeForm β hβ C
      (((1 : ℝ) ⊗ₜ[ℚ] (β : A)) * y) (((1 : ℝ) ⊗ₜ[ℚ] (β : A)) * y) =
      algebraMap ℚ ℝ (n : ℚ)⁻¹ * Langlands.Algebra.regularTrace ℝ (ℝ ⊗[ℚ] A)
        (((1 : ℝ) ⊗ₜ[ℚ] (β : A)) * y *
          (D.realPositiveKottwitzHom C).val.hom Complex.I *
            D.toSecondKindInvolution.rationalInvolution.baseChange ℝ y) := by
  let ρ := D.toSecondKindInvolution.rationalInvolution.baseChange ℝ
  let J := (D.realPositiveKottwitzHom C).val.hom Complex.I
  have hJ : ρ J = -J := by
    simpa only [ρ, J, Complex.star_def, Complex.conj_I, map_neg] using
      (D.realPositiveKottwitzHom C).val.star_compatible Complex.I
  have hb : ρ ((1 : ℝ) ⊗ₜ[ℚ] (β : A)) = -((1 : ℝ) ⊗ₜ[ℚ] (β : A)) := by
    dsimp only [ρ]
    rw [AlgebraInvolution.baseChange_tmul,
      SecondKindInvolution.rationalInvolution_apply, hβ, TensorProduct.tmul_neg]
  have hi : ((1 : ℝ) ⊗ₜ[ℚ] (β : A)) * ((1 : ℝ) ⊗ₜ[ℚ] (↑β⁻¹ : A)) = 1 := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Units.mul_inv,
      ← Algebra.TensorProduct.one_def]
  rw [kottwitzTraceHodgeForm_apply, D.skewTwist_tracePairingBaseChange_apply]
  change _ * Langlands.Algebra.regularTrace ℝ (ℝ ⊗[ℚ] A)
    ((((1 : ℝ) ⊗ₜ[ℚ] (β : A)) * y) * ρ ((((1 : ℝ) ⊗ₜ[ℚ] (β : A)) * y) * J) *
      ((1 : ℝ) ⊗ₜ[ℚ] (↑β⁻¹ : A))) = _
  simp only [ρ.apply_mul, hJ, hb, mul_neg, neg_mul, neg_neg, mul_assoc, hi, mul_one]
  rfl

end Langlands.Shimura.CentralSimpleUnitaryData
