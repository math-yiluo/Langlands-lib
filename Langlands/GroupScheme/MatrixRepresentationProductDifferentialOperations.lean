import Langlands.GroupScheme.MatrixRepresentationProductDifferential
import Langlands.GroupScheme.MatrixRepresentationDifferentialOperations

/-! # Tensor and dual operations on actual finite-product algebraic differentials -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix Kronecker TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.GroupScheme.GeneralLinear.DualNumber
open Langlands.GroupScheme.GeneralLinearProductDualNumber

variable {R : CommRingCat.{u}}
variable {I : Type u} [Finite I]
variable {n : I → Type} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
variable {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
variable {S : Type u} [CommRing S] [Algebra R S]

/-- The differential of the actual common-source tensor scheme representation. -/
theorem productDifferential_tensor (ρ : MatrixRepresentation (groupScheme n R) m)
    (σ : MatrixRepresentation (groupScheme n R) k) (X : ∀ i, Matrix (n i) (n i) S) :
    (ρ.tensor σ).productDifferential S X =
      ρ.productDifferential S X ⊗ₖ (1 : Matrix k k S) +
        (1 : Matrix m m S) ⊗ₖ σ.productDifferential S X := by
  rw [productDifferential_coefficients, tensor_affineMatrix, productDifferential_affineMatrix,
    productDifferential_affineMatrix, coefficients_kronecker_matrixUnit]

/-- The differential of the actual dual scheme representation. -/
theorem productDifferential_dual (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : ∀ i, Matrix (n i) (n i) S) :
    ρ.dual.productDifferential S X = -(ρ.productDifferential S X).transpose := by
  rw [productDifferential_coefficients, dual_affineMatrix, productDifferential_affineMatrix,
    coefficients_contragredient_matrixUnit]

/-- The matrix of the constructed coordinate differential action is the differential itself. -/
@[simp]
theorem productDifferentialAction_toMatrix (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : ∀ i, Matrix (n i) (n i) S) :
    LinearMap.toMatrix' (ρ.productDifferentialAction S X) = ρ.productDifferential S X :=
  LinearMap.toMatrix'_toLin' _

/-- The sum action on the full tensor module, linear in the source matrix family. -/
def productTensorDifferentialAction (ρ : MatrixRepresentation (groupScheme n R) m)
    (σ : MatrixRepresentation (groupScheme n R) k) (S : Type u)
    [CommRing S] [Algebra R S] :
    (∀ i, Matrix (n i) (n i) S) →ₗ[S] Module.End S ((m → S) ⊗[S] (k → S)) where
  toFun X := TensorProduct.map (ρ.productDifferentialAction S X) LinearMap.id +
    TensorProduct.map LinearMap.id (σ.productDifferentialAction S X)
  map_add' X Y := by
    simp only [map_add, TensorProduct.map_add_left, TensorProduct.map_add_right]
    abel
  map_smul' r X := by
    simp only [map_smul, TensorProduct.map_smul_left, TensorProduct.map_smul_right,
      smul_add, RingHom.id_apply]

/-- The constructed full tensor action obeys the sum rule on pure tensors. -/
@[simp]
theorem productTensorDifferentialAction_tmul (ρ : MatrixRepresentation (groupScheme n R) m)
    (σ : MatrixRepresentation (groupScheme n R) k) (X : ∀ i, Matrix (n i) (n i) S)
    (v : m → S) (w : k → S) :
    ρ.productTensorDifferentialAction σ S X (v ⊗ₜ[S] w) =
      (ρ.productDifferentialAction S X v) ⊗ₜ[S] w +
        v ⊗ₜ[S] (σ.productDifferentialAction S X w) := by
  change TensorProduct.map (ρ.productDifferentialAction S X) LinearMap.id (v ⊗ₜ[S] w) +
    TensorProduct.map LinearMap.id (σ.productDifferentialAction S X) (v ⊗ₜ[S] w) = _
  simp only [TensorProduct.map_tmul, LinearMap.id_apply]

/-- Tensor coordinates identify this full module action with the differentiated scheme action. -/
theorem productTensorDifferentialAction_coordinates
    (ρ : MatrixRepresentation (groupScheme n R) m)
    (σ : MatrixRepresentation (groupScheme n R) k) (X : ∀ i, Matrix (n i) (n i) S)
    (v : (m → S) ⊗[S] (k → S)) :
    CoordinateTensor.coordinates S m k (ρ.productTensorDifferentialAction σ S X v) =
      (ρ.tensor σ).productDifferentialAction S X (CoordinateTensor.coordinates S m k v) := by
  change CoordinateTensor.coordinates S m k
    (TensorProduct.map (ρ.productDifferentialAction S X) LinearMap.id v +
      TensorProduct.map LinearMap.id (σ.productDifferentialAction S X) v) = _
  rw [map_add, CoordinateTensor.coordinates_map, CoordinateTensor.coordinates_map,
    productDifferentialAction_toMatrix, productDifferentialAction_toMatrix,
    LinearMap.toMatrix'_id, LinearMap.toMatrix'_id,
    productDifferentialAction_apply, productDifferential_tensor, Matrix.add_mulVec]

/-- The negative transpose action on the full module dual, linear in the source matrix family. -/
def productDualDifferentialAction (ρ : MatrixRepresentation (groupScheme n R) m) (S : Type u)
    [CommRing S] [Algebra R S] :
    (∀ i, Matrix (n i) (n i) S) →ₗ[S] Module.End S (Module.Dual S (m → S)) :=
  (Module.Dual.transpose (R := S) (M := m → S) (M' := m → S)).comp
    (-(ρ.productDifferentialAction S))

@[simp]
theorem productDualDifferentialAction_apply (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : ∀ i, Matrix (n i) (n i) S) (f : Module.Dual S (m → S)) (v : m → S) :
    ρ.productDualDifferentialAction S X f v = -f (ρ.productDifferentialAction S X v) := by
  change f (-(ρ.productDifferentialAction S X v)) = _
  exact map_neg f _

/-- Coordinate evaluation identifies the differentiated dual scheme action with the full dual action. -/
theorem productDualDifferentialAction_coordinates (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : ∀ i, Matrix (n i) (n i) S) (w : m → S) :
    dotProductEquiv S m (ρ.dual.productDifferentialAction S X w) =
      ρ.productDualDifferentialAction S X (dotProductEquiv S m w) := by
  apply LinearMap.ext
  intro v
  rw [productDualDifferentialAction_apply]
  change (ρ.dual.productDifferentialAction S X w) ⬝ᵥ v =
    -(w ⬝ᵥ (ρ.productDifferentialAction S X v))
  rw [productDifferentialAction_apply, productDifferential_dual, Matrix.neg_mulVec, neg_dotProduct,
    dotProduct_comm, Matrix.dotProduct_transpose_mulVec]
  rfl

end Langlands.GroupScheme.MatrixRepresentation
