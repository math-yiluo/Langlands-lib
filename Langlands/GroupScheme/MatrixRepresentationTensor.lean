import Langlands.GroupScheme.MatrixRepresentationDual
import Langlands.GroupScheme.GeneralLinearTensor
import Langlands.Representation.Tensor.Coordinates

/-! # Tensor coefficients of actual group-scheme representations -/

noncomputable section
universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix Kronecker TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Tensor two representations of the same group scheme through the actual GL tensor morphism. -/
def tensor (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m) :
    MatrixRepresentation G (n × m) :=
  lift ρ σ ≫ GeneralLinear.tensorHom n m R

/-- On schemes, the tensor representation pairs the two actual coefficient morphisms. -/
theorem tensor_hom_hom (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m) :
    (ρ.tensor σ).hom.hom =
      lift ρ.hom.hom σ.hom.hom ≫ (GeneralLinear.tensorHom n m R).hom.hom := rfl

/-- Tensor products commute with restriction along any group-scheme morphism. -/
@[simp] theorem tensor_restrict (ρ : MatrixRepresentation G n)
    (σ : MatrixRepresentation G m) (f : H ⟶ G) :
    (ρ.restrict f).tensor (σ.restrict f) = (ρ.tensor σ).restrict f := by
  simp only [tensor, restrict]
  rw [← Category.assoc, comp_lift]

/-- On any test scheme, the tensor coefficient matrix is the Kronecker matrix. -/
@[simp] theorem tensor_pointMatrix (ρ : MatrixRepresentation G n)
    (σ : MatrixRepresentation G m) (T : Over (Spec R)) (x : T ⟶ G.X) :
    (ρ.tensor σ).pointMatrix T x =
      GeneralLinear.kroneckerHom n m Γ(T.left, ⊤) (ρ.pointMatrix T x, σ.pointMatrix T x) := by
  simp only [pointMatrix_apply, tensor_hom_hom, ← Category.assoc, comp_lift]
  exact GeneralLinear.pointsEquiv_lift_tensorHom n m R T _ _

/-- Each tensor coefficient is the product of the corresponding two original coefficients. -/
theorem tensor_pointMatrix_entry (ρ : MatrixRepresentation G n)
    (σ : MatrixRepresentation G m) (T : Over (Spec R)) (x : T ⟶ G.X)
    (i k : n) (j l : m) :
    (ρ.tensor σ).pointMatrix T x (i, j) (k, l) =
      ρ.pointMatrix T x i k * σ.pointMatrix T x j l := by
  rw [tensor_pointMatrix]
  rfl

/-- Over an affine test scheme the Kronecker matrix has entries in the test algebra itself. -/
@[simp] theorem tensor_affineMatrix (ρ : MatrixRepresentation G n)
    (σ : MatrixRepresentation G m) (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ G.X) :
    (ρ.tensor σ).affineMatrix S x =
      GeneralLinear.kroneckerHom n m S (ρ.affineMatrix S x, σ.affineMatrix S x) := by
  simp only [affineMatrix_apply, tensor_hom_hom, ← Category.assoc, comp_lift]
  exact GeneralLinear.affinePointsEquiv_lift_tensorHom n m R S _ _

theorem tensor_affineMatrix_entry (ρ : MatrixRepresentation G n)
    (σ : MatrixRepresentation G m) (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ G.X) (i k : n) (j l : m) :
    (ρ.tensor σ).affineMatrix S x (i, j) (k, l) =
      ρ.affineMatrix S x i k * σ.affineMatrix S x j l := by
  rw [tensor_affineMatrix]
  rfl

/-- Coefficient change acts entrywise on the tensor matrix. -/
theorem tensor_affineMatrix_naturality (ρ : MatrixRepresentation G n)
    (σ : MatrixRepresentation G m) {S S' : CommAlgCat.{u} R} (f : S ⟶ S')
    (x : (algSpec R).obj (op S) ⟶ G.X) :
    (ρ.tensor σ).affineMatrix S' ((algSpec R).map f.op ≫ x) =
      Matrix.GeneralLinearGroup.map f.hom.toRingHom
        (GeneralLinear.kroneckerHom n m S (ρ.affineMatrix S x, σ.affineMatrix S x)) := by
  rw [affineMatrix_naturality, tensor_affineMatrix]

/-- The tensor action on all coordinate vectors is multiplication by the Kronecker matrix. -/
theorem tensor_affineAction (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m)
    (S : CommAlgCat.{u} R) (x : (algSpec R).obj (op S) ⟶ G.X) (v : n × m → S) :
    (ρ.tensor σ).affineAction S x v =
      ((ρ.affineMatrix S x : Matrix n n S) ⊗ₖ
        (σ.affineMatrix S x : Matrix m m S)) *ᵥ v := by
  rw [affineAction_apply, tensor_affineMatrix, GeneralLinear.kroneckerHom_coe]

/-- A decomposable coordinate vector transforms by the two original coefficient actions. -/
theorem tensor_affineAction_decomposable (ρ : MatrixRepresentation G n)
    (σ : MatrixRepresentation G m) (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ G.X) (v : n → S) (w : m → S) :
    (ρ.tensor σ).affineAction S x (fun ij => v ij.1 * w ij.2) =
      fun ij => (ρ.affineAction S x v) ij.1 * (σ.affineAction S x w) ij.2 := by
  rw [affineAction_apply, tensor_affineMatrix]
  exact GeneralLinear.kroneckerHom_mulVec n m _ _ v w

/-- The matrix of the previously constructed affine representation is its coefficient matrix. -/
@[simp] theorem affineRepresentation_toMatrix (ρ : MatrixRepresentation G n)
    (S : CommAlgCat.{u} R) (x : (algSpec R).obj (op S) ⟶ G.X) :
    LinearMap.toMatrix' (ρ.affineRepresentation S x) =
      (ρ.affineMatrix S x : Matrix n n S) := by
  change LinearMap.toMatrix' (Matrix.toLin' (ρ.affineMatrix S x : Matrix n n S)) = _
  exact LinearMap.toMatrix'_toLin' _

/-- The actual tensor scheme representation evaluates to the full tensor representation
transported through the published tensor-basis coordinates. -/
theorem tensor_affineRepresentation (ρ : MatrixRepresentation G n)
    (σ : MatrixRepresentation G m) (S : CommAlgCat.{u} R) :
    (ρ.tensor σ).affineRepresentation S =
      CoordinateTensor.representation (ρ.affineRepresentation S) (σ.affineRepresentation S) := by
  apply MonoidHom.ext
  intro x
  apply LinearMap.ext
  intro v
  rw [affineRepresentation_apply, tensor_affineAction,
    CoordinateTensor.representation_matrix, affineRepresentation_toMatrix,
    affineRepresentation_toMatrix]

/-- The full module tensor product is equivalent to the evaluated tensor scheme representation. -/
def affineTensorEquiv (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m)
    (S : CommAlgCat.{u} R) :
    ((ρ.affineRepresentation S).tprod (σ.affineRepresentation S)).Equiv
      ((ρ.tensor σ).affineRepresentation S) where
  toLinearEquiv := CoordinateTensor.coordinates S n m
  isIntertwining' x := by
    rw [tensor_affineRepresentation]
    exact (CoordinateTensor.equiv (ρ.affineRepresentation S)
      (σ.affineRepresentation S)).isIntertwining' x

@[simp] theorem affineTensorEquiv_tmul (ρ : MatrixRepresentation G n)
    (σ : MatrixRepresentation G m) (S : CommAlgCat.{u} R)
    (v : n → S) (w : m → S) (i : n) (j : m) :
    ρ.affineTensorEquiv σ S (v ⊗ₜ[S] w) (i, j) = v i * w j :=
  CoordinateTensor.coordinates_tmul S n m v w i j

/-- Intertwining holds on every tensor, without a decomposability hypothesis. -/
theorem affineTensorEquiv_intertwining (ρ : MatrixRepresentation G n)
    (σ : MatrixRepresentation G m) (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ G.X) (v : (n → S) ⊗[S] (m → S)) :
    ρ.affineTensorEquiv σ S
        (TensorProduct.map (ρ.affineRepresentation S x) (σ.affineRepresentation S x) v) =
      (ρ.tensor σ).affineAction S x (ρ.affineTensorEquiv σ S v) := by
  exact DFunLike.congr_fun ((ρ.affineTensorEquiv σ S).isIntertwining' x) v

end Langlands.GroupScheme.MatrixRepresentation
