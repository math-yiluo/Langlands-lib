import Langlands.Shimura.Unitary.RationalTrace
import Langlands.Shimura.PEL.Similitudes

/-! # The alternating trace pairing and its two adjoint actions -/

noncomputable section

universe u v w

namespace Langlands.Shimura.AlgebraInvolution

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Conjugating an involution by a skew unit again gives an involution. -/
def skewAdjoint (σ : AlgebraInvolution R A) (β : Aˣ) (hβ : σ (β : A) = -(β : A)) :
    AlgebraInvolution R A where
  linear :=
    { toFun a := (β : A) * σ a * (↑β⁻¹ : A)
      map_add' a b := by simp [mul_add, add_mul]
      map_smul' r a := by simp }
  map_one := by simp
  map_mul a b := by simp [mul_assoc]
  involutive a := by
    have hu : σ.units β = -β := Units.ext hβ
    have hi : σ (↑β⁻¹ : A) = -(↑β⁻¹ : A) := by
      change (σ.units β⁻¹ : A) = _
      rw [σ.units_inv, hu]
      simp
    change (β : A) * σ ((β : A) * σ a * (↑β⁻¹ : A)) * (↑β⁻¹ : A) = a
    simp only [σ.apply_mul, σ.apply_apply, hi, hβ]
    simp [mul_assoc]

@[simp] theorem skewAdjoint_apply (σ : AlgebraInvolution R A) (β : Aˣ)
    (hβ : σ (β : A) = -(β : A)) (a : A) :
    σ.skewAdjoint β hβ a = (β : A) * σ a * (↑β⁻¹ : A) := rfl

theorem apply_skewAdjoint (σ : AlgebraInvolution R A) (β : Aˣ)
    (hβ : σ (β : A) = -(β : A)) (a : A) :
    σ (σ.skewAdjoint β hβ a) = (↑β⁻¹ : A) * a * (β : A) := by
  have hu : σ.units β = -β := Units.ext hβ
  have hi : σ (↑β⁻¹ : A) = -(↑β⁻¹ : A) := by
    change (σ.units β⁻¹ : A) = _
    rw [σ.units_inv, hu]
    simp
  simp [hi, hβ, mul_assoc]

end Langlands.Shimura.AlgebraInvolution

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField Module _root_.Algebra

variable {E : Type u} {K : Type v} {A : Type w}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n) (β : Aˣ)

/-- The source trace formula, on the actual rational vector space of the algebra. -/
def tracePairing : LinearMap.BilinForm ℚ A :=
  (LinearMap.compr₂ (LinearMap.mul ℚ A) D.rationalTrace).compl₁₂
    (LinearMap.mulRight ℚ (β : A)) D.toSecondKindInvolution.rationalInvolution.linear

omit [IsScalarTower E K A] in
@[simp] theorem tracePairing_apply (x y : A) :
    D.tracePairing β x y = D.rationalTrace (x * (β : A) * D.involution y) := rfl

/-- Skewness of the defining unit makes the trace pairing skew-symmetric. -/
theorem tracePairing_skew (hβ : D.involution (β : A) = -(β : A)) (x y : A) :
    D.tracePairing β y x = -D.tracePairing β x y := by
  simp only [tracePairing_apply]
  calc
    D.rationalTrace (y * (β : A) * D.involution x) =
        D.rationalTrace (D.involution (y * (β : A) * D.involution x)) :=
      (D.rationalTrace_involution _).symm
    _ = -D.rationalTrace (x * (β : A) * D.involution y) := by
      simp only [AlgebraInvolution.apply_mul, AlgebraInvolution.apply_apply,
        hβ, neg_mul, mul_neg, map_neg, mul_assoc]

theorem tracePairing_isAlt (hβ : D.involution (β : A) = -(β : A)) :
    (D.tracePairing β).IsAlt := by
  intro x
  have h := D.tracePairing_skew β hβ x x
  linarith

/-- Every unit produces a nondegenerate trace pairing; skewness is needed only
for alternation. -/
theorem tracePairing_nondegenerate : (D.tracePairing β).Nondegenerate := by
  have : Module.Finite E A := Module.Finite.of_basis D.totallyRealBasis
  have : Module.Finite ℚ A := FiniteDimensional.trans ℚ E A
  have : IsSimpleRing A := D.simple
  have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := D.rank_gt_one; omega)
  have hz (a : A) : D.rationalTrace a = 0 ↔
      Langlands.Algebra.regularTrace ℚ A a = 0 := by
    rw [rationalTrace_apply, mul_eq_zero]
    simp [hn]
  have hreg := Langlands.Algebra.regularTraceForm_nondegenerate ℚ A
  constructor
  · intro x hx
    apply hreg.1 x
    intro b
    apply (hz (x * b)).mp
    have h := hx (D.involution ((↑β⁻¹ : A) * b))
    simp only [tracePairing_apply, AlgebraInvolution.apply_apply] at h
    simpa only [← mul_assoc, Units.mul_inv_cancel_right] using h
  · intro y hy
    have hzero : (β : A) * D.involution y = 0 := by
      apply hreg.2
      intro x
      apply (hz (x * ((β : A) * D.involution y))).mp
      simpa only [tracePairing_apply, mul_assoc] using hy x
    have hσ : D.involution y = 0 := by
      have h := congrArg (fun a : A => (↑β⁻¹ : A) * a) hzero
      simpa [← mul_assoc] using h
    have h := congrArg D.involution hσ
    simpa using h

omit [IsScalarTower E K A] in
/-- The left algebra action is adjoint for the original involution. -/
theorem tracePairing_left (b x y : A) :
    D.tracePairing β (b * x) y = D.tracePairing β x (D.involution b * y) := by
  simp only [tracePairing_apply, AlgebraInvolution.apply_mul,
    AlgebraInvolution.apply_apply]
  simpa only [mul_assoc] using D.rationalTrace_mul_comm b (x * (β : A) * D.involution y)

/-- The actual PEL involution adjoint to right multiplication. -/
def tracePairingAdjoint (hβ : D.involution (β : A) = -(β : A)) :
    AlgebraInvolution ℚ A :=
  D.toSecondKindInvolution.rationalInvolution.skewAdjoint β hβ

omit [IsScalarTower E K A] in
@[simp] theorem tracePairingAdjoint_apply
    (hβ : D.involution (β : A) = -(β : A)) (b : A) :
    D.tracePairingAdjoint β hβ b = (β : A) * D.involution b * (↑β⁻¹ : A) := rfl

omit [IsScalarTower E K A] in
/-- Right multiplication is adjoint for the beta-conjugated involution. -/
theorem tracePairing_right (hβ : D.involution (β : A) = -(β : A)) (b x y : A) :
    D.tracePairing β (x * b) y =
      D.tracePairing β x (y * D.tracePairingAdjoint β hβ b) := by
  simp only [tracePairing_apply, AlgebraInvolution.apply_mul]
  have h : D.involution (D.tracePairingAdjoint β hβ b) =
      (↑β⁻¹ : A) * b * (β : A) :=
    D.toSecondKindInvolution.rationalInvolution.apply_skewAdjoint β hβ b
  rw [h]
  simp [mul_assoc]

omit [IsScalarTower E K A] in
/-- The commuting left and right multiplication actions have exactly the two
adjoints in the source formula. -/
theorem tracePairing_bimodule (hβ : D.involution (β : A) = -(β : A))
    (b₁ b₂ x y : A) :
    D.tracePairing β (b₁ * x * b₂) y =
      D.tracePairing β x (D.involution b₁ * y * D.tracePairingAdjoint β hβ b₂) := by
  rw [D.tracePairing_right β hβ, D.tracePairing_left]
  simp only [mul_assoc]

omit [IsScalarTower E K A] in
/-- Compatibility with the existing PEL bilinear-similitude interface. -/
theorem tracePairing_respectsInvolution :
    PEL.FormRespectsInvolution D.toSecondKindInvolution.rationalInvolution
      (D.tracePairing β) :=
  D.tracePairing_left β

end Langlands.Shimura.CentralSimpleUnitaryData
