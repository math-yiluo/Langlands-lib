import Langlands.Shimura.PEL.PositiveInput
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-! # Scalar extension of the normalized PEL trace pairing -/

noncomputable section

universe u v w z

open scoped TensorProduct

namespace Langlands.Algebra

theorem regularTrace_tmul {R S A : Type*} [CommRing R] [CommRing S]
    [Ring A] [Algebra R S] [Algebra R A] [Module.Free R A] [Module.Finite R A]
    (s : S) (a : A) :
    regularTrace S (S ⊗[R] A) (s ⊗ₜ[R] a) =
      s * algebraMap R S (regularTrace R A a) := by
  have h : s ⊗ₜ[R] a = s • ((1 : S) ⊗ₜ[R] a) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h, map_smul, smul_eq_mul, regularTrace_one_tmul]

end Langlands.Algebra

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField Module _root_.Algebra

variable {E : Type u} {K : Type v} {A : Type w}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
    (S : Type z) [CommRing S] [Algebra ℚ S] (β : Aˣ)

/-- The actual scalar extension of the rational trace form. -/
def tracePairingBaseChange : LinearMap.BilinForm S (S ⊗[ℚ] A) :=
  (D.tracePairing β).baseChange S

omit [IsScalarTower E K A] in
@[simp] theorem tracePairingBaseChange_tmul (s t : S) (a b : A) :
    D.tracePairingBaseChange S β (s ⊗ₜ[ℚ] a) (t ⊗ₜ[ℚ] b) =
      algebraMap ℚ S (D.tracePairing β a b) * (s * t) := by
  simp only [tracePairingBaseChange, LinearMap.BilinForm.baseChange_tmul,
    _root_.Algebra.smul_def]

omit [IsScalarTower E K A] in
/-- The extended form is the normalized regular-trace formula on the tensor algebra. -/
theorem tracePairingBaseChange_apply (x y : S ⊗[ℚ] A) :
    D.tracePairingBaseChange S β x y =
      algebraMap ℚ S (n : ℚ)⁻¹ *
        Langlands.Algebra.regularTrace S (S ⊗[ℚ] A)
          (x * ((1 : S) ⊗ₜ[ℚ] (β : A)) *
            D.toSecondKindInvolution.rationalInvolution.baseChange S y) := by
  have : FiniteDimensional K A := D.finite
  have : FiniteDimensional ℚ A := FiniteDimensional.trans ℚ K A
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply, add_mul, hx, hx', mul_add]
  | tmul s a =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' =>
      simp only [map_add, mul_add, hy, hy']
    | tmul t b =>
      simp only [tracePairingBaseChange_tmul, tracePairing_apply, rationalTrace_apply,
        AlgebraInvolution.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, Langlands.Algebra.regularTrace_tmul, map_mul,
        SecondKindInvolution.rationalInvolution_apply]
      ring

theorem tracePairingBaseChange_skew
    (hβ : D.involution (β : A) = -(β : A)) (x y : S ⊗[ℚ] A) :
    D.tracePairingBaseChange S β y x = -D.tracePairingBaseChange S β x y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply, hx, hx', neg_add]
  | tmul s a =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' =>
      simp only [map_add, LinearMap.add_apply, hy, hy', neg_add]
    | tmul t b =>
      rw [tracePairingBaseChange_tmul, tracePairingBaseChange_tmul,
        D.tracePairing_skew β hβ, map_neg, neg_mul, mul_comm t s]

theorem tracePairingBaseChange_isAlt
    (hβ : D.involution (β : A) = -(β : A)) :
    (D.tracePairingBaseChange S β).IsAlt := by
  intro x
  have h := D.tracePairingBaseChange_skew S β hβ x x
  have h2 : (2 : ℚ) • D.tracePairingBaseChange S β x x = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp h
  have hhalf := congrArg (fun s : S => (1 / 2 : ℚ) • s) h2
  simpa only [smul_smul, show (1 / 2 : ℚ) * 2 = 1 by norm_num,
    one_smul, smul_zero] using hhalf

omit [IsScalarTower E K A] in
/-- Canceling the auxiliary twist gives a form with the original right adjoint. -/
theorem skewTwist_tracePairingBaseChange_apply
    (hβ : D.involution (β : A) = -(β : A)) (x y : S ⊗[ℚ] A) :
    (D.skewTwist β hβ).tracePairingBaseChange S β⁻¹ x y =
      algebraMap ℚ S (n : ℚ)⁻¹ *
        Langlands.Algebra.regularTrace S (S ⊗[ℚ] A)
          (x * D.toSecondKindInvolution.rationalInvolution.baseChange S y *
            ((1 : S) ⊗ₜ[ℚ] (↑β⁻¹ : A))) := by
  rw [tracePairingBaseChange_apply]
  have ht (y : S ⊗[ℚ] A) :
      (D.skewTwist β hβ).toSecondKindInvolution.rationalInvolution.baseChange S y =
        ((1 : S) ⊗ₜ[ℚ] (β : A)) *
          D.toSecondKindInvolution.rationalInvolution.baseChange S y *
            ((1 : S) ⊗ₜ[ℚ] (↑β⁻¹ : A)) := by
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, mul_add, add_mul, hy, hy']
    | tmul s a => simp [Algebra.TensorProduct.tmul_mul_tmul]
  have hinv :
      ((1 : S) ⊗ₜ[ℚ] (↑β⁻¹ : A)) * ((1 : S) ⊗ₜ[ℚ] (β : A)) = 1 := by
    simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.one_def]
  rw [ht]
  congr 2
  calc
    x * ((1 : S) ⊗ₜ[ℚ] (↑β⁻¹ : A)) *
        (((1 : S) ⊗ₜ[ℚ] (β : A)) *
          D.toSecondKindInvolution.rationalInvolution.baseChange S y *
            ((1 : S) ⊗ₜ[ℚ] (↑β⁻¹ : A))) =
        x * (((1 : S) ⊗ₜ[ℚ] (↑β⁻¹ : A)) *
          ((1 : S) ⊗ₜ[ℚ] (β : A))) *
          D.toSecondKindInvolution.rationalInvolution.baseChange S y *
            ((1 : S) ⊗ₜ[ℚ] (↑β⁻¹ : A)) := by simp only [mul_assoc]
    _ = _ := by rw [hinv, mul_one]

end Langlands.Shimura.CentralSimpleUnitaryData
