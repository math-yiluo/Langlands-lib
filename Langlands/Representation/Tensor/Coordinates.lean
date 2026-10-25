import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.RepresentationTheory.Intertwining

/-! # Finite-coordinate realizations of full tensor representations -/

noncomputable section
universe u v w z

open scoped TensorProduct Matrix Kronecker

namespace Langlands.CoordinateTensor

variable (R : Type u) [CommRing R]
variable (n : Type v) (m : Type w)
variable [Fintype n] [Fintype m]

/-- Coordinates in the tensor product of the standard bases. -/
def coordinates : ((n → R) ⊗[R] (m → R)) ≃ₗ[R] (n × m → R) :=
  ((Pi.basisFun R n).tensorProduct (Pi.basisFun R m)).equivFun

@[simp] theorem coordinates_tmul (v : n → R) (w : m → R) (i : n) (j : m) :
    coordinates R n m (v ⊗ₜ[R] w) (i, j) = v i * w j := by
  simp [coordinates, Module.Basis.equivFun_apply,
    Module.Basis.tensorProduct_repr_tmul_apply, mul_comm]

/-- The inverse sends decomposable coordinate vectors to pure tensors. -/
@[simp] theorem coordinates_symm_mul (v : n → R) (w : m → R) :
    (coordinates R n m).symm (fun p => v p.1 * w p.2) = v ⊗ₜ[R] w := by
  apply (coordinates R n m).injective
  ext ⟨i, j⟩
  simp

/-- Tensoring two linear maps acts through the Kronecker product of their matrices. -/
theorem coordinates_map [DecidableEq n] [DecidableEq m] (f : (n → R) →ₗ[R] (n → R))
    (g : (m → R) →ₗ[R] (m → R)) (x : (n → R) ⊗[R] (m → R)) :
    coordinates R n m (TensorProduct.map f g x) =
      (LinearMap.toMatrix' f ⊗ₖ LinearMap.toMatrix' g) *ᵥ coordinates R n m x := by
  have h := LinearMap.toMatrix_mulVec_repr
    ((Pi.basisFun R n).tensorProduct (Pi.basisFun R m))
    ((Pi.basisFun R n).tensorProduct (Pi.basisFun R m)) (TensorProduct.map f g) x
  simpa only [coordinates, Module.Basis.equivFun_apply, TensorProduct.toMatrix_map,
    LinearMap.toMatrix_eq_toMatrix'] using h.symm

variable {R n m}
variable {G : Type z} [Monoid G]
variable (ρ : Representation R G (n → R)) (σ : Representation R G (m → R))

/-- The full module tensor representation transported to the product coordinate type. -/
def representation : Representation R G (n × m → R) :=
  (coordinates R n m).conjRingEquiv.toMonoidHom.comp (ρ.tprod σ)

@[simp] theorem representation_apply (a : G) (x : n × m → R) :
    representation ρ σ a x =
      coordinates R n m (TensorProduct.map (ρ a) (σ a) ((coordinates R n m).symm x)) := rfl

/-- The coordinate realization is equivalent to the full algebraic tensor representation. -/
def equiv : (ρ.tprod σ).Equiv (representation ρ σ) where
  toLinearEquiv := coordinates R n m
  isIntertwining' a := by
    apply LinearMap.ext
    intro x
    simp [representation_apply]

@[simp] theorem equiv_tmul (v : n → R) (w : m → R) (i : n) (j : m) :
    equiv ρ σ (v ⊗ₜ[R] w) (i, j) = v i * w j :=
  coordinates_tmul R n m v w i j

/-- The coordinate tensor action is the usual Kronecker matrix action. -/
theorem representation_matrix [DecidableEq n] [DecidableEq m] (a : G) (x : n × m → R) :
    representation ρ σ a x =
      (LinearMap.toMatrix' (ρ a) ⊗ₖ LinearMap.toMatrix' (σ a)) *ᵥ x := by
  rw [representation_apply, coordinates_map, LinearEquiv.apply_symm_apply]

/-- A decomposable vector transforms by applying the two original actions. -/
theorem representation_decomposable (a : G) (v : n → R) (w : m → R) :
    representation ρ σ a (fun p => v p.1 * w p.2) =
      fun p => (ρ a v) p.1 * (σ a w) p.2 := by
  rw [representation_apply, coordinates_symm_mul, TensorProduct.map_tmul]
  ext ⟨i, j⟩
  exact coordinates_tmul R n m _ _ i j

end Langlands.CoordinateTensor
