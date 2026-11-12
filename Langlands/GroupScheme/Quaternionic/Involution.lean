import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Data.Matrix.Basic

/-!
# Involutions of the first kind

An involution of the first kind of an algebra `A` over a commutative ring `K` is a
`K`-linear anti-automorphism of order two. This module defines them, their spaces of
symmetric and alternating elements, the conjugate-transpose involution they induce on
square matrices, and their extension of scalars to commutative `K`-algebras.
-/

noncomputable section

universe u v w

open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic

/-- An involution of the first kind of a `K`-algebra `A`: a `K`-linear map `σ : A → A`
with `σ 1 = 1`, `σ (x * y) = σ y * σ x` and `σ (σ x) = x`. Linearity over `K` means that
`σ` fixes the centre's scalars `K`, which is the meaning of "first kind". -/
structure FirstKindInvolution (K : Type u) (A : Type v) [CommRing K] [Ring A] [Algebra K A]
    where
  /-- The underlying `K`-linear map. -/
  toLinearMap : A →ₗ[K] A
  map_one' : toLinearMap 1 = 1
  map_mul' : ∀ x y, toLinearMap (x * y) = toLinearMap y * toLinearMap x
  involutive' : ∀ x, toLinearMap (toLinearMap x) = x

namespace FirstKindInvolution

variable {K : Type u} {A : Type v} [CommRing K] [Ring A] [Algebra K A]
  (σ : FirstKindInvolution K A)

instance : CoeFun (FirstKindInvolution K A) (fun _ => A → A) := ⟨fun σ => σ.toLinearMap⟩

@[simp] theorem coe_toLinearMap : ⇑σ.toLinearMap = σ := rfl

@[simp] theorem map_one : σ 1 = 1 := σ.map_one'

@[simp] theorem map_mul (x y : A) : σ (x * y) = σ y * σ x := σ.map_mul' x y

@[simp] theorem apply_apply (x : A) : σ (σ x) = x := σ.involutive' x

@[simp] theorem map_add (x y : A) : σ (x + y) = σ x + σ y := σ.toLinearMap.map_add x y

@[simp] theorem map_zero : σ 0 = 0 := σ.toLinearMap.map_zero

@[simp] theorem map_neg (x : A) : σ (-x) = -σ x := σ.toLinearMap.map_neg x

@[simp] theorem map_sub (x y : A) : σ (x - y) = σ x - σ y := σ.toLinearMap.map_sub x y

@[simp] theorem map_smul (c : K) (x : A) : σ (c • x) = c • σ x := σ.toLinearMap.map_smul c x

@[simp] theorem map_sum {ι : Type w} (s : Finset ι) (f : ι → A) :
    σ (∑ i ∈ s, f i) = ∑ i ∈ s, σ (f i) :=
  _root_.map_sum σ.toLinearMap f s

/-- An involution of the first kind fixes the scalars. -/
@[simp] theorem map_algebraMap (c : K) : σ (algebraMap K A c) = algebraMap K A c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one]

theorem injective : Function.Injective σ :=
  Function.LeftInverse.injective σ.apply_apply

/-- The space `A^σ` of symmetric elements, `{x | σ x = x}`. -/
def symmetricSubspace : Submodule K A := LinearMap.ker (σ.toLinearMap - LinearMap.id)

theorem mem_symmetricSubspace {x : A} : x ∈ σ.symmetricSubspace ↔ σ x = x := by
  simp [symmetricSubspace, sub_eq_zero]

/-- The space of alternating (trace-type) elements `{a - σ a | a ∈ A}`. -/
def alternatingSubspace : Submodule K A := LinearMap.range (LinearMap.id - σ.toLinearMap)

theorem mem_alternatingSubspace {x : A} :
    x ∈ σ.alternatingSubspace ↔ ∃ a, a - σ a = x := by
  simp [alternatingSubspace]

theorem sub_mem_alternatingSubspace (a : A) : a - σ a ∈ σ.alternatingSubspace :=
  σ.mem_alternatingSubspace.2 ⟨a, rfl⟩

/-! ### The conjugate transpose on square matrices -/

section Matrix

variable (n : Type w) [Fintype n] [DecidableEq n]

/-- The `σ`-conjugate transpose `x ↦ ᵗx^σ`, `(ᵗx^σ) i j = σ (x j i)`, as an involution of
the first kind of the matrix algebra `M_n(A)`. -/
def matrix : FirstKindInvolution K (Matrix n n A) where
  toLinearMap :=
    { toFun := fun x => Matrix.of fun i j => σ (x j i)
      map_add' := fun x y => by
        ext i j
        simp
      map_smul' := fun c x => by
        ext i j
        simp }
  map_one' := by
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.one_apply, h, Ne.symm h]
  map_mul' := fun x y => by
    ext i j
    simp [Matrix.mul_apply]
  involutive' := fun x => by
    ext i j
    simp

variable {n}

@[simp] theorem matrix_apply (x : Matrix n n A) (i j : n) : σ.matrix n x i j = σ (x j i) :=
  rfl

end Matrix

/-! ### Extension of scalars -/

section BaseChange

variable (R : Type w) [CommRing R] [Algebra K R]

/-- The `R`-linear extension `id_R ⊗ σ` of `σ` to `R ⊗[K] A`, again an involution of the
first kind (over `R`). -/
def baseChange : FirstKindInvolution R (R ⊗[K] A) where
  toLinearMap := σ.toLinearMap.baseChange R
  map_one' := by
    rw [Algebra.TensorProduct.one_def, LinearMap.baseChange_tmul, coe_toLinearMap, map_one]
  map_mul' := fun x y => by
    induction x using TensorProduct.inductionOn with
    | add x x' hx hx' => simp [add_mul, mul_add, hx, hx']
    | tmul r a =>
      induction y using TensorProduct.inductionOn with
      | add y y' hy hy' => simp [add_mul, mul_add, hy, hy']
      | tmul s b =>
        simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm r s]
  involutive' := fun x => by
    induction x using TensorProduct.inductionOn with
    | add x x' hx hx' => rw [LinearMap.map_add, LinearMap.map_add, hx, hx']
    | tmul r a => simp

variable {R}

@[simp] theorem baseChange_tmul (r : R) (a : A) :
    σ.baseChange R (r ⊗ₜ[K] a) = r ⊗ₜ[K] σ a :=
  LinearMap.baseChange_tmul _ _ _

/-- Extension of scalars commutes with every change of coefficient algebra. -/
theorem map_baseChange {S : Type w} [CommRing S] [Algebra K S] (φ : R →ₐ[K] S)
    (x : R ⊗[K] A) :
    Algebra.TensorProduct.map φ (AlgHom.id K A) (σ.baseChange R x) =
      σ.baseChange S (Algebra.TensorProduct.map φ (AlgHom.id K A) x) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => rw [LinearMap.map_add, _root_.map_add, _root_.map_add, hx, hx',
      LinearMap.map_add]
  | tmul r a => simp

end BaseChange

end FirstKindInvolution

end Langlands.GroupScheme.Quaternionic
