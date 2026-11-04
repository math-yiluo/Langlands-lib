import Langlands.GroupScheme.MatrixRepresentation
import Langlands.GroupScheme.Lie.KernelTargetMaps
import Langlands.GroupScheme.Lie.GeneralLinearAdjoint

/-! # Actual tangent matrices for arbitrary algebraic representations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
variable {n : Type} [Fintype n] [DecidableEq n]
variable (ρ : MatrixRepresentation G n) (A : Type u) [CommRing A] [Algebra R A]

/-- The matrix of the image of an actual tangent vector under an algebraic
representation, extracted from its actual dual-number point. -/
def tangentMatrix (X : lieKernel G A) : Matrix n n A :=
  GeneralLinear.DualNumber.pointKernelEquiv.symm (Lie.targetMap ρ A X)

/-- Reconstructing the matrix recovers the actual image tangent point. -/
@[simp] theorem pointKernelEquiv_tangentMatrix (X : lieKernel G A) :
    GeneralLinear.DualNumber.pointKernelEquiv (ρ.tangentMatrix A X) =
      Lie.targetMap ρ A X := Equiv.apply_symm_apply _ _

/-- The identity of the raw kernel represents the zero tangent vector. -/
@[simp] theorem tangentMatrix_one : ρ.tangentMatrix A 1 = 0 := by
  unfold tangentMatrix
  rw [map_one]
  exact congrArg Multiplicative.toAdd
    (map_one (GeneralLinear.DualNumber.pointKernelMulEquiv (n := n) (R := R) (S := A)).symm)

/-- The actual kernel product gives matrix addition. -/
theorem tangentMatrix_mul (X Y : lieKernel G A) :
    ρ.tangentMatrix A (X * Y) = ρ.tangentMatrix A X + ρ.tangentMatrix A Y := by
  unfold tangentMatrix
  rw [map_mul]
  exact congrArg Multiplicative.toAdd
    ((GeneralLinear.DualNumber.pointKernelMulEquiv (n := n) (R := R) (S := A)).symm.map_mul _ _)

/-- Epsilon scaling gives scalar multiplication of the extracted matrix. -/
theorem tangentMatrix_scale (c : A) (X : lieKernel G A) :
    ρ.tangentMatrix A (lieKernelScale G c X) = c • ρ.tangentMatrix A X := by
  unfold tangentMatrix
  rw [lieKernelTarget_scale]
  exact GeneralLinear.DualNumber.pointKernelEquiv_symm_scale c _

/-- The actual tangent matrices form a linear differential for affine source. -/
def kernelDifferential [IsAffineHom G.X.hom] :
    Additive (lieKernel G A) →ₗ[A] Matrix n n A :=
  (GeneralLinear.DualNumber.pointKernelLinearEquiv (n := n) (R := R) (A := A)).symm.toLinearMap.comp
    (Lie.targetMapLinear ρ A)

@[simp] theorem kernelDifferential_apply [IsAffineHom G.X.hom]
    (X : Additive (lieKernel G A)) :
    ρ.kernelDifferential A X = ρ.tangentMatrix A X.toMul := rfl

variable {A} {B : Type u} [CommRing B] [Algebra R B]

/-- Matrices of tangent vectors commute with arbitrary coefficient extension. -/
theorem tangentMatrix_naturality (f : A →ₐ[R] B) (X : lieKernel G A) :
    ρ.tangentMatrix B (lieKernelMap G f X) = (ρ.tangentMatrix A X).map f := by
  unfold tangentMatrix
  rw [lieKernelTarget_map]
  exact GeneralLinear.DualNumber.pointKernelEquiv_symm_naturality f _

/-- Restricting a representation is composition of its actual kernel maps. -/
theorem tangentMatrix_restrict (f : H ⟶ G) (X : lieKernel H A) :
    (ρ.restrict f).tangentMatrix A X = ρ.tangentMatrix A (Lie.targetMap f A X) := by
  unfold tangentMatrix
  congr 1

end Langlands.GroupScheme.MatrixRepresentation
