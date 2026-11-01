import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Module.Lattice

/-! # Unique rational extension of homomorphisms from a full integer order -/

noncomputable section

open Module

universe uI uJ uA uR uR'

namespace Langlands.IntegralOrderExtension

variable {I : Type uI} {J : Type uJ}
variable {A : Type uA} [Ring A] [Algebra ℚ A]
variable {R : Type uR} [Ring R] [Algebra ℚ R]
variable {R' : Type uR'} [Ring R'] [Algebra ℚ R']
variable {O : Subalgebra ℤ A} [Submodule.IsLattice ℚ O.toSubmodule]

/-- Extend basis values along the rational basis supplied by the full lattice. -/
def linear (b : Basis I ℤ O) (f : O →+* R) : A →ₗ[ℚ] R :=
  (b.extendOfIsLattice (M := O.toSubmodule) ℚ).constr ℚ (fun i => f (b i))

@[simp] theorem linear_basis (b : Basis I ℤ O) (f : O →+* R) (i : I) :
    linear b f (b i : A) = f (b i) := by
  simpa only [linear, Basis.extendOfIsLattice_apply] using
    (b.extendOfIsLattice (M := O.toSubmodule) ℚ).constr_basis ℚ (fun i => f (b i)) i

/-- The rational-linear extension agrees with the supplied map on every order element. -/
@[simp] theorem linear_coe (b : Basis I ℤ O) (f : O →+* R) (x : O) :
    linear b f (x : A) = f x := by
  have h : ((linear b f).restrictScalars ℤ).comp O.val.toLinearMap =
      f.toIntAlgHom.toLinearMap := by
    apply b.ext
    intro i
    exact linear_basis b f i
  exact DFunLike.congr_fun h x

theorem linear_map_mul (b : Basis I ℤ O) (f : O →+* R) :
    ∀ x y, linear b f (x * y) = linear b f x * linear b f y := by
  apply (LinearMap.map_mul_iff (linear b f)).2
  apply (b.extendOfIsLattice (M := O.toSubmodule) ℚ).ext
  intro i
  apply (b.extendOfIsLattice (M := O.toSubmodule) ℚ).ext
  intro j
  change linear b f (b.extendOfIsLattice (M := O.toSubmodule) ℚ i * b.extendOfIsLattice (M := O.toSubmodule) ℚ j) =
    linear b f (b.extendOfIsLattice (M := O.toSubmodule) ℚ i) * linear b f (b.extendOfIsLattice (M := O.toSubmodule) ℚ j)
  simp only [Basis.extendOfIsLattice_apply]
  change linear b f ((b i * b j : O) : A) =
    linear b f (b i : A) * linear b f (b j : A)
  simp only [linear_coe, map_mul]

/-- An actual ring map from the full order extends to a rational algebra map. -/
def extend (b : Basis I ℤ O) (f : O →+* R) : A →ₐ[ℚ] R :=
  AlgHom.ofLinearMap (linear b f)
    (by simpa only [Subalgebra.coe_one, map_one] using linear_coe b f (1 : O))
    (linear_map_mul b f)

@[simp] theorem extend_coe (b : Basis I ℤ O) (f : O →+* R) (x : O) :
    extend b f (x : A) = f x :=
  linear_coe b f x

/-- Rational algebra maps are determined by their restrictions to the full order. -/
theorem algHom_ext (b : Basis I ℤ O) {f g : A →ₐ[ℚ] R}
    (h : ∀ x : O, f (x : A) = g (x : A)) : f = g := by
  have hl : f.toLinearMap = g.toLinearMap := by
    apply (b.extendOfIsLattice (M := O.toSubmodule) ℚ).ext
    intro i
    simpa only [Basis.extendOfIsLattice_apply, AlgHom.toLinearMap_apply] using h (b i)
  exact AlgHom.ext (fun x => DFunLike.congr_fun hl x)

theorem extend_unique (b : Basis I ℤ O) (f : O →+* R) (g : A →ₐ[ℚ] R)
    (h : ∀ x : O, g (x : A) = f x) : extend b f = g := by
  apply algHom_ext b
  intro x
  exact (extend_coe b f x).trans (h x).symm

/-- Restrict a rational algebra map to the original integer order. -/
def restrict (f : A →ₐ[ℚ] R) : O →+* R :=
  f.toRingHom.comp O.val.toRingHom

omit [Submodule.IsLattice ℚ O.toSubmodule] in
@[simp] theorem restrict_apply (f : A →ₐ[ℚ] R) (x : O) :
    restrict (O := O) f x = f (x : A) := rfl

@[simp] theorem restrict_extend (b : Basis I ℤ O) (f : O →+* R) :
    restrict (extend b f) = f :=
  RingHom.ext (extend_coe b f)

@[simp] theorem extend_restrict (b : Basis I ℤ O) (f : A →ₐ[ℚ] R) :
    extend b (restrict f) = f :=
  extend_unique b (restrict f) f (fun _ => rfl)

/-- Ring maps from the order into a rational algebra are exactly rational algebra maps. -/
def equiv (b : Basis I ℤ O) : (O →+* R) ≃ (A →ₐ[ℚ] R) where
  toFun := extend b
  invFun := restrict
  left_inv := restrict_extend b
  right_inv := extend_restrict b

/-- Uniqueness makes the extension independent of the selected integer basis. -/
theorem extend_basis_independent (b : Basis I ℤ O) (b' : Basis J ℤ O) (f : O →+* R) :
    extend b f = extend b' f :=
  extend_unique b f (extend b' f) (extend_coe b' f)

/-- Unique extension commutes with every rational algebra map of target algebras. -/
theorem extend_natural (b : Basis I ℤ O) (f : O →+* R) (g : R →ₐ[ℚ] R') :
    extend b (g.toRingHom.comp f) = g.comp (extend b f) := by
  apply algHom_ext b
  intro x
  simp only [extend_coe, RingHom.comp_apply, AlgHom.comp_apply]
  rfl

end Langlands.IntegralOrderExtension
