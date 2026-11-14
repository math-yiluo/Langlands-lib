import Langlands.GroupScheme.VectorMatrixMap
import Mathlib.LinearAlgebra.Matrix.Transvection

/-! # Actual scheme kernels of square matrix maps over fields -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.VectorGroup

private theorem matrixIso_square {R : CommRingCat.{u}} {n : ℕ}
    (A B : (Matrix (Fin n) (Fin n) R)ˣ) (c : Fin n → R)
    (M : Matrix (Fin n) (Fin n) R)
    (hmat : Matrix.diagonal c * (B : Matrix (Fin n) (Fin n) R) =
      ((A⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R) * M) :
    (matrixIso (R := R) B).hom ≫ diagonal (R := R) c =
      matrixHom (R := R) M ≫ (matrixIso (R := R) A).inv := by
  change matrixHom (R := R) (B : Matrix (Fin n) (Fin n) R) ≫ diagonal (R := R) c =
    matrixHom (R := R) M ≫ matrixHom (R := R)
      ((A⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R)
  rw [← matrixHom_diagonal, matrixHom_comp, matrixHom_comp]
  exact congrArg (fun N : Matrix (Fin n) (Fin n) R => matrixHom (R := R) N) hmat

variable {k : Type u} [Field k] {n : ℕ}

/-- The inverse of a product of elementary transvections is the reversed
product of their elementary inverses. -/
private def transvectionProductUnit (L : List (Matrix.TransvectionStruct (Fin n) k)) :
    (Matrix (Fin n) (Fin n) k)ˣ where
  val := (L.map Matrix.TransvectionStruct.toMatrix).prod
  inv := (L.reverse.map (Matrix.TransvectionStruct.toMatrix ∘
    Matrix.TransvectionStruct.inv)).prod
  val_inv := Matrix.TransvectionStruct.prod_mul_reverse_inv_prod L
  inv_val := Matrix.TransvectionStruct.reverse_inv_prod_mul_prod L

/-- Diagonalization over the ground field gives an actual isomorphism of
scheme-theoretic kernels with a polynomial vector group. -/
theorem exists_matrixKernelIso (M : Matrix (Fin n) (Fin n) k) :
    ∃ d : ℕ, Nonempty (kernel (matrixHom (R := CommRingCat.of k) M) ≅
      groupScheme (CommRingCat.of k) d) := by
  classical
  obtain ⟨L, L', c, hM⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  let A := transvectionProductUnit L
  let B := transvectionProductUnit L'
  have hfactor : M = (A : Matrix (Fin n) (Fin n) k) * Matrix.diagonal c *
      (B : Matrix (Fin n) (Fin n) k) := hM
  have hmat : Matrix.diagonal c * (B : Matrix (Fin n) (Fin n) k) =
      ((A⁻¹ : (Matrix (Fin n) (Fin n) k)ˣ) : Matrix (Fin n) (Fin n) k) * M := by
    rw [hfactor, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul,
      Matrix.one_mul]
  have hsquare :
      (matrixIso (R := CommRingCat.of k) B).hom ≫ diagonal (R := CommRingCat.of k) c =
        matrixHom (R := CommRingCat.of k) M ≫
          (matrixIso (R := CommRingCat.of k) A).inv :=
    matrixIso_square (R := CommRingCat.of k) A B c M hmat
  exact ⟨Fintype.card {j : Fin n // c j = 0},
    ⟨kernelSquareIso (matrixHom (R := CommRingCat.of k) M)
      (diagonal (R := CommRingCat.of k) c)
      (matrixIso (R := CommRingCat.of k) B) (matrixIso (R := CommRingCat.of k) A).symm
      hsquare ≪≫ diagonalKernelIso c⟩⟩

/-- A chosen dimension of the actual matrix kernel. -/
def matrixKernelDimension (M : Matrix (Fin n) (Fin n) k) : ℕ :=
  Classical.choose (exists_matrixKernelIso M)

/-- The actual matrix kernel is a vector group over its original field. -/
def matrixKernelIso (M : Matrix (Fin n) (Fin n) k) :
    kernel (matrixHom (R := CommRingCat.of k) M) ≅
      groupScheme (CommRingCat.of k) (matrixKernelDimension M) :=
  Classical.choice (Classical.choose_spec (exists_matrixKernelIso M))

/-- Every square matrix map over a field has a smooth connected unipotent
actual scheme-theoretic kernel. -/
theorem matrix_kernel_properties (M : Matrix (Fin n) (Fin n) k) :
    Smooth (kernel (matrixHom (R := CommRingCat.of k) M)).X.hom ∧
      ConnectedSpace (kernel (matrixHom (R := CommRingCat.of k) M)).X.left ∧
        IsUnipotent (kernel (matrixHom (R := CommRingCat.of k) M)) := by
  let d := matrixKernelDimension M
  let hv : RelativeRoot.IsVectorGroupOfDimension
      (groupScheme (CommRingCat.of k) d) d :=
    ⟨coordinates (CommRingCat.of k) d, isNaturalVectorCoordinates⟩
  exact smooth_connected_unipotent_of_groupIso (matrixKernelIso M)
    ⟨hv.smooth, hv.connectedSpace, isUnipotent k d⟩

/-- The same actual kernel geometry after every ring-to-field specialization.
No rank assumption on the specialized coefficient matrix is required. -/
theorem matrix_baseChange_kernel_properties {R : CommRingCat.{u}}
    (ρ : R ⟶ CommRingCat.of k) (M : Matrix (Fin n) (Fin n) R) :
    Smooth (kernel ((GroupScheme.baseChange (Spec.map ρ)).map (matrixHom M))).X.hom ∧
      ConnectedSpace
        (kernel ((GroupScheme.baseChange (Spec.map ρ)).map (matrixHom M))).X.left ∧
      IsUnipotent (kernel ((GroupScheme.baseChange (Spec.map ρ)).map (matrixHom M))) := by
  exact smooth_connected_unipotent_of_groupIso
    (kernelSquareIso _ _ (baseChangeIso ρ) (baseChangeIso ρ)
      (matrixHom_baseChange ρ M)) (matrix_kernel_properties (M.map ρ.hom))

end Langlands.GroupScheme.VectorGroup
