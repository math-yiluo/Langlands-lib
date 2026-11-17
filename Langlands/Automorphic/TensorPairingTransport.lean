import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.Analysis.Complex.Basic

/-! # Tensoring and transporting nonzero invariant bilinear forms -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Automorphic.TensorPairing

open scoped TensorProduct

universe uA uB uW

variable {A : Type uA} [AddCommGroup A] [Module ℂ A]
  {B : Type uB} [AddCommGroup B] [Module ℂ B]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The complex bilinear form obtained by tensoring two factor forms. -/
def tensorForm (C : A →ₗ[ℂ] A →ₗ[ℂ] ℂ) (D : B →ₗ[ℂ] B →ₗ[ℂ] ℂ) :
    A ⊗[ℂ] B →ₗ[ℂ] A ⊗[ℂ] B →ₗ[ℂ] ℂ :=
  LinearMap.BilinForm.tensorDistrib ℂ ℂ (C ⊗ₜ[ℂ] D)

@[simp]
theorem tensorForm_tmul (C : A →ₗ[ℂ] A →ₗ[ℂ] ℂ) (D : B →ₗ[ℂ] B →ₗ[ℂ] ℂ)
    (a a' : A) (b b' : B) :
    tensorForm C D (a ⊗ₜ[ℂ] b) (a' ⊗ₜ[ℂ] b') = C a a' * D b b' := by
  change D b b' * C a a' = C a a' * D b b'
  exact mul_comm _ _

private theorem exists_bilinear_ne_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V] (C : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hC : C ≠ 0) :
    ∃ x y, C x y ≠ 0 := by
  by_contra h
  apply hC
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact not_not.mp fun hxy => h ⟨x, y, hxy⟩

theorem tensorForm_ne_zero (C : A →ₗ[ℂ] A →ₗ[ℂ] ℂ) (D : B →ₗ[ℂ] B →ₗ[ℂ] ℂ)
    (hC : C ≠ 0) (hD : D ≠ 0) : tensorForm C D ≠ 0 := by
  obtain ⟨a, a', ha⟩ := exists_bilinear_ne_zero C hC
  obtain ⟨b, b', hb⟩ := exists_bilinear_ne_zero D hD
  intro hzero
  have hval := congrArg
    (fun E : A ⊗[ℂ] B →ₗ[ℂ] A ⊗[ℂ] B →ₗ[ℂ] ℂ =>
      E (a ⊗ₜ[ℂ] b) (a' ⊗ₜ[ℂ] b')) hzero
  exact mul_ne_zero ha hb (by simpa only [tensorForm_tmul, LinearMap.zero_apply] using hval)

/-- Independent invariance on both factors gives invariance of the tensor form. -/
theorem tensorForm_invariant
    (C : A →ₗ[ℂ] A →ₗ[ℂ] ℂ) (D : B →ₗ[ℂ] B →ₗ[ℂ] ℂ)
    (P Q : Module.End ℂ A) (R S : Module.End ℂ B)
    (hC : ∀ a a', C (P a) (Q a') = C a a')
    (hD : ∀ b b', D (R b) (S b') = D b b') (x y : A ⊗[ℂ] B) :
    tensorForm C D (TensorProduct.map P R x) (TensorProduct.map Q S y) =
      tensorForm C D x y := by
  induction x with
  | tmul a b =>
    induction y with
    | tmul a' b' => simp only [TensorProduct.map_tmul, tensorForm_tmul, hC, hD]
    | add y y' hy hy' => simp only [map_add, hy, hy']
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']

/-- The infinitesimal skew-invariance identity on the first factor persists under tensoring. -/
theorem tensorForm_lie_left
    (C : A →ₗ[ℂ] A →ₗ[ℂ] ℂ) (D : B →ₗ[ℂ] B →ₗ[ℂ] ℂ)
    (P Q : Module.End ℂ A) (hC : ∀ a a', C (P a) a' + C a (Q a') = 0)
    (x y : A ⊗[ℂ] B) :
    tensorForm C D (TensorProduct.map P LinearMap.id x) y +
      tensorForm C D x (TensorProduct.map Q LinearMap.id y) = 0 := by
  induction x with
  | tmul a b =>
    induction y with
    | tmul a' b' =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, tensorForm_tmul]
      rw [← add_mul, hC, zero_mul]
    | add y y' hy hy' =>
      simp only [map_add]
      rw [add_add_add_comm, hy, hy', zero_add]
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply]
    rw [add_add_add_comm, hx, hx', zero_add]

/-- The corresponding infinitesimal identity on the residual factor also persists. -/
theorem tensorForm_lie_right
    (C : A →ₗ[ℂ] A →ₗ[ℂ] ℂ) (D : B →ₗ[ℂ] B →ₗ[ℂ] ℂ)
    (R S : Module.End ℂ B) (hD : ∀ b b', D (R b) b' + D b (S b') = 0)
    (x y : A ⊗[ℂ] B) :
    tensorForm C D (TensorProduct.map LinearMap.id R x) y +
      tensorForm C D x (TensorProduct.map LinearMap.id S y) = 0 := by
  induction x with
  | tmul a b =>
    induction y with
    | tmul a' b' =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, tensorForm_tmul]
      rw [← mul_add, hD, mul_zero]
    | add y y' hy hy' =>
      simp only [map_add]
      rw [add_add_add_comm, hy, hy', zero_add]
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply]
    rw [add_add_add_comm, hx, hx', zero_add]

/-- Transport the tensor form onto the carrier of an actual tensor equivalence. -/
def transport (e : A ⊗[ℂ] B ≃ₗ[ℂ] W)
    (C : A →ₗ[ℂ] A →ₗ[ℂ] ℂ) (D : B →ₗ[ℂ] B →ₗ[ℂ] ℂ) :
    W →ₗ[ℂ] W →ₗ[ℂ] ℂ :=
  LinearMap.BilinForm.congr e (tensorForm C D)

@[simp]
theorem transport_apply (e : A ⊗[ℂ] B ≃ₗ[ℂ] W)
    (C : A →ₗ[ℂ] A →ₗ[ℂ] ℂ) (D : B →ₗ[ℂ] B →ₗ[ℂ] ℂ) (x y : W) :
    transport e C D x y = tensorForm C D (e.symm x) (e.symm y) := rfl

theorem transport_ne_zero (e : A ⊗[ℂ] B ≃ₗ[ℂ] W)
    (C : A →ₗ[ℂ] A →ₗ[ℂ] ℂ) (D : B →ₗ[ℂ] B →ₗ[ℂ] ℂ)
    (hC : C ≠ 0) (hD : D ≠ 0) : transport e C D ≠ 0 := by
  intro hzero
  apply tensorForm_ne_zero C D hC hD
  exact (LinearMap.BilinForm.congr e).injective (hzero.trans (map_zero _).symm)

/-- Covariance of a tensor equivalence carries product invariance to the actual carrier. -/
theorem transport_invariant (e : A ⊗[ℂ] B ≃ₗ[ℂ] W)
    (C : A →ₗ[ℂ] A →ₗ[ℂ] ℂ) (D : B →ₗ[ℂ] B →ₗ[ℂ] ℂ)
    (P Q : Module.End ℂ A) (R S : Module.End ℂ B) (T U : Module.End ℂ W)
    (hC : ∀ a a', C (P a) (Q a') = C a a')
    (hD : ∀ b b', D (R b) (S b') = D b b')
    (heT : ∀ t, e (TensorProduct.map P R t) = T (e t))
    (heU : ∀ t, e (TensorProduct.map Q S t) = U (e t)) (x y : W) :
    transport e C D (T x) (U y) = transport e C D x y := by
  obtain ⟨a, rfl⟩ := e.surjective x
  obtain ⟨b, rfl⟩ := e.surjective y
  simp only [transport_apply, ← heT, ← heU, e.symm_apply_apply]
  exact tensorForm_invariant C D P Q R S hC hD a b

/-- Infinitesimal covariance on the first factor transfers its skew-invariance identity. -/
theorem transport_lie_left (e : A ⊗[ℂ] B ≃ₗ[ℂ] W)
    (C : A →ₗ[ℂ] A →ₗ[ℂ] ℂ) (D : B →ₗ[ℂ] B →ₗ[ℂ] ℂ)
    (P Q : Module.End ℂ A) (T U : Module.End ℂ W)
    (hC : ∀ a a', C (P a) a' + C a (Q a') = 0)
    (heT : ∀ t, e (TensorProduct.map P LinearMap.id t) = T (e t))
    (heU : ∀ t, e (TensorProduct.map Q LinearMap.id t) = U (e t)) (x y : W) :
    transport e C D (T x) y + transport e C D x (U y) = 0 := by
  obtain ⟨a, rfl⟩ := e.surjective x
  obtain ⟨b, rfl⟩ := e.surjective y
  simp only [transport_apply, ← heT, ← heU, e.symm_apply_apply]
  exact tensorForm_lie_left C D P Q hC a b

/-- Infinitesimal covariance on the residual factor transfers its skew-invariance identity. -/
theorem transport_lie_right (e : A ⊗[ℂ] B ≃ₗ[ℂ] W)
    (C : A →ₗ[ℂ] A →ₗ[ℂ] ℂ) (D : B →ₗ[ℂ] B →ₗ[ℂ] ℂ)
    (R S : Module.End ℂ B) (T U : Module.End ℂ W)
    (hD : ∀ b b', D (R b) b' + D b (S b') = 0)
    (heT : ∀ t, e (TensorProduct.map LinearMap.id R t) = T (e t))
    (heU : ∀ t, e (TensorProduct.map LinearMap.id S t) = U (e t)) (x y : W) :
    transport e C D (T x) y + transport e C D x (U y) = 0 := by
  obtain ⟨a, rfl⟩ := e.surjective x
  obtain ⟨b, rfl⟩ := e.surjective y
  simp only [transport_apply, ← heT, ← heU, e.symm_apply_apply]
  exact tensorForm_lie_right C D R S hD a b

end Langlands.Automorphic.TensorPairing
