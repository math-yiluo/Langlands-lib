import Langlands.GroupScheme.MatrixRepresentationDifferential
import Langlands.GroupScheme.MatrixRepresentationTensor

/-! # Tensor and dual operations on actual algebraic differentials -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix Kronecker TensorProduct

namespace Langlands.GroupScheme.GeneralLinear.DualNumber

variable {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
variable {S : Type u} [CommRing S]

/-- The first-order coefficient of a Kronecker product is the Kronecker sum. -/
theorem coefficients_kronecker_matrixUnit (A : Matrix m m S) (B : Matrix k k S) :
    coefficients (kroneckerHom m k (DualNumber S) (matrixUnit A, matrixUnit B)) =
      A ⊗ₖ (1 : Matrix k k S) + (1 : Matrix m m S) ⊗ₖ B := by
  apply Matrix.ext
  rintro ⟨i, j⟩ ⟨l, t⟩
  change TrivSqZeroExt.snd
    (((matrixUnit A : Matrix m m (DualNumber S)) i l) *
      ((matrixUnit B : Matrix k k (DualNumber S)) j t)) =
    A i l * (1 : Matrix k k S) j t + (1 : Matrix m m S) i l * B j t
  by_cases hi : i = l <;> by_cases hj : j = t <;>
    simp [matrixUnit_val, Matrix.one_apply, hi, hj, TrivSqZeroExt.snd_mul,
      smul_eq_mul, add_comm]

/-- Inverse transpose changes the first-order coefficient to its negative transpose. -/
theorem coefficients_contragredient_matrixUnit (A : Matrix m m S) :
    coefficients (matrixContragredient m (DualNumber S) (matrixUnit A)) = -A.transpose := by
  apply Matrix.ext
  intro i j
  change TrivSqZeroExt.snd
    ((((matrixUnit A)⁻¹ : GL m (DualNumber S)) : Matrix m m (DualNumber S)) j i) =
    -(A j i)
  rw [matrixUnit_inv_val]
  by_cases h : j = i <;> simp [h]

end Langlands.GroupScheme.GeneralLinear.DualNumber

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.GroupScheme.GeneralLinear Langlands.GroupScheme.GeneralLinear.DualNumber

variable {R : CommRingCat.{u}}
variable {n m k : Type} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
variable {S : Type u} [CommRing S] [Algebra R S]

/-- The differential of the actual common-source tensor scheme representation. -/
theorem differential_tensor (ρ : MatrixRepresentation (groupScheme n R) m)
    (σ : MatrixRepresentation (groupScheme n R) k) (X : Matrix n n S) :
    (ρ.tensor σ).differential S X =
      ρ.differential S X ⊗ₖ (1 : Matrix k k S) +
        (1 : Matrix m m S) ⊗ₖ σ.differential S X := by
  rw [differential_coefficients, tensor_affineMatrix, differential_affineMatrix,
    differential_affineMatrix, coefficients_kronecker_matrixUnit]

/-- The differential of the actual dual scheme representation. -/
theorem differential_dual (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : Matrix n n S) :
    ρ.dual.differential S X = -(ρ.differential S X).transpose := by
  rw [differential_coefficients, dual_affineMatrix, differential_affineMatrix,
    coefficients_contragredient_matrixUnit]

/-- The matrix of the constructed coordinate differential action is the differential itself. -/
@[simp]
theorem differentialAction_toMatrix (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : Matrix n n S) :
    LinearMap.toMatrix' (ρ.differentialAction S X) = ρ.differential S X :=
  LinearMap.toMatrix'_toLin' _

/-- The sum action on the full tensor module, linear in the source matrix. -/
def tensorDifferentialAction (ρ : MatrixRepresentation (groupScheme n R) m)
    (σ : MatrixRepresentation (groupScheme n R) k) (S : Type u)
    [CommRing S] [Algebra R S] :
    Matrix n n S →ₗ[S] Module.End S ((m → S) ⊗[S] (k → S)) where
  toFun X := TensorProduct.map (ρ.differentialAction S X) LinearMap.id +
    TensorProduct.map LinearMap.id (σ.differentialAction S X)
  map_add' X Y := by
    simp only [map_add, TensorProduct.map_add_left, TensorProduct.map_add_right]
    abel
  map_smul' r X := by
    simp only [map_smul, TensorProduct.map_smul_left, TensorProduct.map_smul_right,
      smul_add, RingHom.id_apply]

/-- The constructed full tensor action obeys the sum rule on pure tensors. -/
@[simp]
theorem tensorDifferentialAction_tmul (ρ : MatrixRepresentation (groupScheme n R) m)
    (σ : MatrixRepresentation (groupScheme n R) k) (X : Matrix n n S)
    (v : m → S) (w : k → S) :
    ρ.tensorDifferentialAction σ S X (v ⊗ₜ[S] w) =
      (ρ.differentialAction S X v) ⊗ₜ[S] w +
        v ⊗ₜ[S] (σ.differentialAction S X w) := by
  change TensorProduct.map (ρ.differentialAction S X) LinearMap.id (v ⊗ₜ[S] w) +
    TensorProduct.map LinearMap.id (σ.differentialAction S X) (v ⊗ₜ[S] w) = _
  simp only [TensorProduct.map_tmul, LinearMap.id_apply]

/-- Tensor coordinates identify this full module action with the differentiated scheme action. -/
theorem tensorDifferentialAction_coordinates
    (ρ : MatrixRepresentation (groupScheme n R) m)
    (σ : MatrixRepresentation (groupScheme n R) k) (X : Matrix n n S)
    (v : (m → S) ⊗[S] (k → S)) :
    CoordinateTensor.coordinates S m k (ρ.tensorDifferentialAction σ S X v) =
      (ρ.tensor σ).differentialAction S X (CoordinateTensor.coordinates S m k v) := by
  change CoordinateTensor.coordinates S m k
    (TensorProduct.map (ρ.differentialAction S X) LinearMap.id v +
      TensorProduct.map LinearMap.id (σ.differentialAction S X) v) = _
  rw [map_add, CoordinateTensor.coordinates_map, CoordinateTensor.coordinates_map,
    differentialAction_toMatrix, differentialAction_toMatrix,
    LinearMap.toMatrix'_id, LinearMap.toMatrix'_id,
    differentialAction_apply, differential_tensor, Matrix.add_mulVec]

/-- The negative transpose action on the full module dual, linear in the source matrix. -/
def dualDifferentialAction (ρ : MatrixRepresentation (groupScheme n R) m) (S : Type u)
    [CommRing S] [Algebra R S] :
    Matrix n n S →ₗ[S] Module.End S (Module.Dual S (m → S)) :=
  (Module.Dual.transpose (R := S) (M := m → S) (M' := m → S)).comp
    (-(ρ.differentialAction S))

@[simp]
theorem dualDifferentialAction_apply (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : Matrix n n S) (f : Module.Dual S (m → S)) (v : m → S) :
    ρ.dualDifferentialAction S X f v = -f (ρ.differentialAction S X v) := by
  change f (-(ρ.differentialAction S X v)) = _
  exact map_neg f _

/-- Coordinate evaluation identifies the differentiated dual scheme action with the full dual action. -/
theorem dualDifferentialAction_coordinates (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : Matrix n n S) (w : m → S) :
    dotProductEquiv S m (ρ.dual.differentialAction S X w) =
      ρ.dualDifferentialAction S X (dotProductEquiv S m w) := by
  apply LinearMap.ext
  intro v
  rw [dualDifferentialAction_apply]
  change (ρ.dual.differentialAction S X w) ⬝ᵥ v =
    -(w ⬝ᵥ (ρ.differentialAction S X v))
  rw [differentialAction_apply, differential_dual, Matrix.neg_mulVec, neg_dotProduct,
    dotProduct_comm, Matrix.dotProduct_transpose_mulVec]
  rfl

end Langlands.GroupScheme.MatrixRepresentation
