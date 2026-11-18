import Langlands.GroupScheme.OddOrthogonalMatrix.TangentPoints

/-! # Matrix coordinates on the actual odd dual-number identity kernel -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix

open GeneralLinear.DualNumber

variable {l : Type} [Fintype l] [DecidableEq l] (K : Type u) [Field K]

local notation "𝔻" => CommAlgCat.of (CommRingCat.of K) (DualNumber K)
local notation "𝐆" => groupScheme l K

/-- An actual odd identity tangent point maps into the ordinary matrix
identity kernel over the dual numbers. -/
def tangentMatrixKernel (x : lieKernel (groupScheme l K) K) : MatrixKernel (Index l) K :=
  ⟨affineMatrix K 𝔻 x.val, by
    have h := congrArg (affineMatrix K (CommAlgCat.of (CommRingCat.of K) K)) x.property
    change affineMatrix K (CommAlgCat.of (CommRingCat.of K) K)
      ((algSpec (CommRingCat.of K)).map
        (CommAlgCat.ofHom (TrivSqZeroExt.fstHom K K K)).op ≫ x.val) =
        affineMatrix K (CommAlgCat.of (CommRingCat.of K) K) 1 at h
    rw [affineMatrix_naturality, _root_.map_one] at h
    exact h⟩

/-- The epsilon coefficient of an actual identity tangent point. -/
def tangentCoefficient (x : lieKernel (groupScheme l K) K) : Matrix (Index l) (Index l) K :=
  coefficients (affineMatrix K 𝔻 x.val)

/-- Actual odd tangent matrices have exactly the standard `1+εY` expression. -/
theorem matrixUnit_tangentCoefficient (x : lieKernel (groupScheme l K) K) :
    matrixUnit (tangentCoefficient K x) = affineMatrix K 𝔻 x.val :=
  matrixUnit_coefficients (tangentMatrixKernel K x)

/-- The coefficient matrix of every actual odd tangent point satisfies the
alternating linear defect and trace-zero equations. -/
theorem tangentCoefficient_mem (x : lieKernel (groupScheme l K) K) :
    tangentCoefficient K x ∈ lieMatrices := by
  apply (one_add_epsilonMatrix_equations_iff _).1
  have h := affineMatrix_equations K 𝔻 x.val
  have hm := congrArg (fun g : Matrix.GeneralLinearGroup (Index l) (DualNumber K) =>
    (g : Matrix (Index l) (Index l) (DualNumber K))) (matrixUnit_tangentCoefficient K x)
  change 1 + epsilonMatrix (tangentCoefficient K x) =
    (affineMatrix K 𝔻 x.val : Matrix (Index l) (Index l) (DualNumber K)) at hm
  rw [hm]
  exact h

/-- Every matrix in the linearized submodule defines an actual tangent-kernel
point, compatibly with addition and tangent-point multiplication. -/
def tangentKernelMap : Multiplicative (lieMatrices (l := l) (K := K)) →*
    lieKernel (groupScheme l K) K where
  toFun Y := ⟨tangentPoint K Y.toAdd.val Y.toAdd.property,
    tangentPoint_reduction K Y.toAdd.val Y.toAdd.property⟩
  map_one' := by
    apply Subtype.ext
    change tangentPoint K (0 : Matrix (Index l) (Index l) K) _ = 1
    apply affineMatrix_injective K 𝔻
    rw [affineMatrix_tangentPoint, (affineMatrix K 𝔻).map_one]
    exact matrixUnit_zero
  map_mul' Y Z := by
    apply Subtype.ext
    change tangentPoint K (Y.toAdd.val + Z.toAdd.val) _ =
      tangentPoint K Y.toAdd.val Y.toAdd.property * tangentPoint K Z.toAdd.val Z.toAdd.property
    apply affineMatrix_injective K 𝔻
    rw [(affineMatrix K 𝔻).map_mul, affineMatrix_tangentPoint,
      affineMatrix_tangentPoint, affineMatrix_tangentPoint]
    exact matrixUnit_add Y.toAdd.val Z.toAdd.val

/-- The actual matrix of the tangent-kernel construction. -/
theorem affineMatrix_tangentKernelMap (Y : Multiplicative (lieMatrices (l := l) (K := K))) :
    affineMatrix K 𝔻 (tangentKernelMap K Y).val = matrixUnit Y.toAdd.val :=
  affineMatrix_tangentPoint K Y.toAdd.val Y.toAdd.property

/-- The matrix tangent-kernel construction is injective. -/
theorem tangentKernelMap_injective : Function.Injective (tangentKernelMap (l := l) K) := by
  intro Y Z h
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  have hc := congrArg (fun x : lieKernel (groupScheme l K) K =>
    coefficients (affineMatrix K 𝔻 x.val)) h
  change coefficients (affineMatrix K 𝔻
    (tangentPoint K Y.toAdd.val Y.toAdd.property)) =
      coefficients (affineMatrix K 𝔻 (tangentPoint K Z.toAdd.val Z.toAdd.property)) at hc
  rw [affineMatrix_tangentPoint, affineMatrix_tangentPoint,
    coefficients_matrixUnit, coefficients_matrixUnit] at hc
  exact hc

/-- Every actual odd tangent-kernel point is obtained from its coefficient matrix. -/
theorem tangentKernelMap_surjective : Function.Surjective (tangentKernelMap (l := l) K) := by
  intro x
  refine ⟨Multiplicative.ofAdd ⟨tangentCoefficient K x, tangentCoefficient_mem K x⟩, ?_⟩
  apply Subtype.ext
  apply affineMatrix_injective K 𝔻
  rw [affineMatrix_tangentKernelMap]
  exact matrixUnit_tangentCoefficient K x

/-- The actual dual-number identity kernel of the odd norm-one group is the
additive group of the explicit alternating-defect/trace-zero matrix submodule. -/
def tangentKernelEquiv : Multiplicative (lieMatrices (l := l) (K := K)) ≃*
    lieKernel (groupScheme l K) K :=
  MulEquiv.ofBijective (tangentKernelMap K)
    ⟨tangentKernelMap_injective K, tangentKernelMap_surjective K⟩

end Langlands.GroupScheme.OddOrthogonalMatrix
