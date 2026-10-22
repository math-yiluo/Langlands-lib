import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Algebra involutions and scalar extension

The involution fixes the specified base ring. Scalar extension acts as the
identity on the new coefficient ring, including when that ring is complex.
-/

universe u v w z

namespace Langlands.Shimura

/-- A linear, unital, multiplication-reversing involution of an algebra. -/
structure AlgebraInvolution (R : Type u) (A : Type v)
    [CommRing R] [Ring A] [Algebra R A] where
  linear : A →ₗ[R] A
  map_one : linear 1 = 1
  map_mul (a b : A) : linear (a * b) = linear b * linear a
  involutive : Function.Involutive linear

namespace AlgebraInvolution

variable {R : Type u} {A : Type v}
variable [CommRing R] [Ring A] [Algebra R A]

instance : CoeFun (AlgebraInvolution R A) (fun _ => A → A) :=
  ⟨fun σ => σ.linear⟩

variable (σ : AlgebraInvolution R A)

@[simp] theorem apply_one : σ 1 = 1 := σ.map_one
@[simp] theorem apply_zero : σ 0 = 0 := σ.linear.map_zero
@[simp] theorem apply_add (a b : A) : σ (a + b) = σ a + σ b := σ.linear.map_add a b
@[simp] theorem apply_mul (a b : A) : σ (a * b) = σ b * σ a := σ.map_mul a b
@[simp] theorem apply_apply (a : A) : σ (σ a) = a := σ.involutive a
@[simp] theorem apply_smul (r : R) (a : A) : σ (r • a) = r • σ a :=
  σ.linear.map_smul r a

@[simp] theorem apply_algebraMap (r : R) : σ (algebraMap R A r) = algebraMap R A r := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact σ.apply_smul r 1 |>.trans (congrArg (fun a => r • a) σ.apply_one)

/-- Reuse an existing Mathlib star that fixes the base ring. -/
def ofStar [StarRing R] [TrivialStar R] [StarRing A] [StarModule R A] :
    AlgebraInvolution R A where
  linear :=
    { toFun := star
      map_add' := star_add
      map_smul' := fun r a => by simp [star_smul] }
  map_one := star_one A
  map_mul := star_mul
  involutive := fun a => star_star a

/-- The induced multiplication-reversing bijection on the actual units. -/
def units (a : Aˣ) : Aˣ where
  val := σ a
  inv := σ (↑a⁻¹ : A)
  val_inv := by rw [← σ.apply_mul, a.inv_mul, σ.apply_one]
  inv_val := by rw [← σ.apply_mul, a.mul_inv, σ.apply_one]

@[simp] theorem units_val (a : Aˣ) : (σ.units a : A) = σ a := rfl
@[simp] theorem units_one : σ.units 1 = 1 := Units.ext σ.apply_one
@[simp] theorem units_mul (a b : Aˣ) : σ.units (a * b) = σ.units b * σ.units a :=
  Units.ext (σ.apply_mul a b)
@[simp] theorem units_inv (a : Aˣ) : σ.units a⁻¹ = (σ.units a)⁻¹ := Units.ext rfl
@[simp] theorem units_units (a : Aˣ) : σ.units (σ.units a) = a :=
  Units.ext (σ.apply_apply a)

/-- Composing the involution with inversion gives a group automorphism. -/
def inverseUnits : Aˣ ≃* Aˣ where
  toFun a := σ.units a⁻¹
  invFun a := σ.units a⁻¹
  left_inv a := by simp
  right_inv a := by simp
  map_mul' a b := by simp

section BaseChange

variable (S : Type w) [CommRing S] [Algebra R S]
open scoped TensorProduct

/-- Extend the involution by `s ⊗ a ↦ s ⊗ σ(a)`, fixing `S` pointwise. -/
noncomputable def baseChange : AlgebraInvolution S (S ⊗[R] A) where
  linear := σ.linear.baseChange S
  map_one := by simp [Algebra.TensorProduct.one_def, σ.map_one]
  map_mul x y := by
    induction x using TensorProduct.inductionOn with
    | add x x' hx hx' => simp [add_mul, mul_add, hx, hx']
    | tmul s a =>
      induction y using TensorProduct.inductionOn with
      | add y y' hy hy' => simp [add_mul, mul_add, hy, hy']
      | tmul t b =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.baseChange_tmul,
          σ.map_mul]
        rw [mul_comm s t]
  involutive x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | tmul s a => simp only [LinearMap.baseChange_tmul, σ.involutive a]

@[simp] theorem baseChange_tmul (s : S) (a : A) :
    σ.baseChange S (s ⊗ₜ[R] a) = s ⊗ₜ[R] σ a := rfl

variable {S} {T : Type z} [CommRing T] [Algebra R T]

/-- Coefficient change on the actual tensor-product algebras. -/
noncomputable def changeCoefficients (f : S →ₐ[R] T) :
    S ⊗[R] A →ₐ[R] T ⊗[R] A :=
  Algebra.TensorProduct.map f (AlgHom.id R A)

@[simp] theorem changeCoefficients_tmul (f : S →ₐ[R] T) (s : S) (a : A) :
    changeCoefficients (A := A) f (s ⊗ₜ[R] a) = f s ⊗ₜ[R] a := rfl

theorem changeCoefficients_involution (f : S →ₐ[R] T) (x : S ⊗[R] A) :
    changeCoefficients f (σ.baseChange S x) =
      σ.baseChange T (changeCoefficients f x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul s a => rfl

@[simp] theorem changeCoefficients_scalar (f : S →ₐ[R] T) (s : S) :
    changeCoefficients (A := A) f (algebraMap S (S ⊗[R] A) s) =
      algebraMap T (T ⊗[R] A) (f s) := by
  simp [Algebra.TensorProduct.algebraMap_apply]

@[simp] theorem changeCoefficients_id :
    changeCoefficients (A := A) (AlgHom.id R S) = AlgHom.id R (S ⊗[R] A) :=
  Algebra.TensorProduct.map_id

theorem changeCoefficients_comp {U : Type*} [CommRing U] [Algebra R U]
    (f : S →ₐ[R] T) (g : T →ₐ[R] U) :
    changeCoefficients (A := A) (g.comp f) =
      (changeCoefficients g).comp (changeCoefficients f) :=
  by
    apply Algebra.TensorProduct.ext'
    intro s a
    rfl

end BaseChange

end AlgebraInvolution
end Langlands.Shimura
