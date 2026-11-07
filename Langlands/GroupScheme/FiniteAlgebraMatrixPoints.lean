import Langlands.GroupScheme.FiniteAlgebraUnits
import Mathlib.RingTheory.MatrixAlgebra

/-! # Actual matrix points of finite-algebra unit group schemes -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.FiniteAlgebraUnits

namespace MatrixPoints

variable {m : Type} [Fintype m] [DecidableEq m]
  (k D : Type u) [Field k] [Ring D] [Algebra k D]

/-- Moving a commutative scalar extension through the actual finite matrix algebra. -/
def coefficientEquiv (R : Type u) [CommRing R] [Algebra k R] :
    R ⊗[k] Matrix m m D ≃ₐ[k] Matrix m m (R ⊗[k] D) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[k] R)
    (matrixEquivTensor m k D)).trans
    ((Algebra.TensorProduct.assoc k k k R D (Matrix m m k)).symm.trans
      (matrixEquivTensor m k (R ⊗[k] D)).symm)

/-- The comparison sends a scalar tensor matrix unit to its actual tensor coefficient. -/
theorem coefficientEquiv_tmul_single (R : Type u) [CommRing R] [Algebra k R]
    (r : R) (a : D) (i j : m) :
    coefficientEquiv k D R (r ⊗ₜ[k] Matrix.single i j a) =
      Matrix.single i j (r ⊗ₜ[k] a) := by
  simp [coefficientEquiv, Matrix.map_single, Matrix.smul_single]

/-- On every pure tensor the comparison is the entrywise scalar extension. -/
theorem coefficientEquiv_tmul (R : Type u) [CommRing R] [Algebra k R]
    (r : R) (M : Matrix m m D) (i j : m) :
    coefficientEquiv k D R (r ⊗ₜ[k] M) i j = r ⊗ₜ[k] M i j := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  simp [TensorProduct.tmul_sum, coefficientEquiv_tmul_single, Matrix.sum_apply,
    Matrix.single_apply, ite_and]

/-- Actual coefficient change commutes with the matrix/tensor comparison. -/
theorem coefficientEquiv_naturality {R S : Type u} [CommRing R] [Algebra k R]
    [CommRing S] [Algebra k S] (f : R →ₐ[k] S) (x : R ⊗[k] Matrix m m D) :
    coefficientEquiv k D S (Algebra.TensorProduct.map f (AlgHom.id k (Matrix m m D)) x) =
      (coefficientEquiv k D R x).map (Algebra.TensorProduct.map f (AlgHom.id k D)) := by
  induction x using TensorProduct.inductionOn with
  | tmul r M =>
    ext i j
    simp [coefficientEquiv_tmul]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    ext i j
    exact (map_add (Algebra.TensorProduct.map f (AlgHom.id k D)) _ _).symm

/-- The matrix comparison is compatible with the actual base-field tensor-unit map. -/
theorem coefficientEquiv_lid (x : k ⊗[k] Matrix m m D) :
    (coefficientEquiv k D k x).map (Algebra.TensorProduct.lid k D) =
      Algebra.TensorProduct.lid k (Matrix m m D) x := by
  induction x using TensorProduct.inductionOn with
  | tmul r M =>
    ext i j
    simp [coefficientEquiv_tmul, Algebra.TensorProduct.lid_tmul, Matrix.smul_apply]
  | add x y hx hy =>
    rw [map_add, Matrix.map_add _ (map_add _), hx, hy, map_add]

variable {d : ℕ} (b : Module.Basis (Fin d) k (Matrix m m D))

/-- Actual affine coefficient points are invertible matrices over the coefficient tensor algebra. -/
def affineMatrixEquiv (R : CommAlgCat.{u} (CommRingCat.of k)) :
    ((algSpec (CommRingCat.of k)).obj (op R) ⟶ (groupScheme b).X) ≃*
      Matrix.GeneralLinearGroup m (R ⊗[k] D) :=
  (affinePointsEquiv b R).trans (Units.mapEquiv (coefficientEquiv k D R).toMulEquiv)

/-- The actual affine matrix comparison respects every coefficient-algebra map. -/
theorem affineMatrixEquiv_naturality {R S : CommAlgCat.{u} (CommRingCat.of k)}
    (f : R ⟶ S) (x : (algSpec (CommRingCat.of k)).obj (op R) ⟶ (groupScheme b).X) :
    affineMatrixEquiv k D b S ((algSpec (CommRingCat.of k)).map f.op ≫ x) =
      Units.map (RingHom.mapMatrix
        (Algebra.TensorProduct.map f.hom (AlgHom.id k D)).toRingHom).toMonoidHom
        (affineMatrixEquiv k D b R x) := by
  apply Units.ext
  change coefficientEquiv k D S
      (affinePointsEquiv b S ((algSpec (CommRingCat.of k)).map f.op ≫ x) :
        S ⊗[k] Matrix m m D) =
    (coefficientEquiv k D R (affinePointsEquiv b R x : R ⊗[k] Matrix m m D)).map
      (Algebra.TensorProduct.map f.hom (AlgHom.id k D))
  erw [FiniteAlgebraUnits.affinePointsEquiv_naturality b f x]
  exact coefficientEquiv_naturality k D f.hom _

/-- Actual unit-group points of the matrix algebra are invertible tensor-coefficient matrices. -/
def tensorMatrixEquiv (T : Over (base k)) :
    (T ⟶ (groupScheme b).X) ≃*
      Matrix.GeneralLinearGroup m (((algΓ (CommRingCat.of k)).obj T).unop ⊗[k] D) :=
  (pointsEquiv b T).trans
    (Units.mapEquiv
      (coefficientEquiv k D ((algΓ (CommRingCat.of k)).obj T).unop).toMulEquiv)

/-- Every actual test pullback acts by the actual coefficient tensor map entrywise. -/
theorem tensorMatrixEquiv_naturality {T T' : Over (base k)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme b).X) :
    tensorMatrixEquiv k D b T' (a ≫ x) =
      Units.map (RingHom.mapMatrix
        (Algebra.TensorProduct.map
          ((algΓ (CommRingCat.of k)).map a).unop.hom (AlgHom.id k D)).toRingHom).toMonoidHom
        (tensorMatrixEquiv k D b T x) := by
  apply Units.ext
  change coefficientEquiv k D ((algΓ (CommRingCat.of k)).obj T').unop
      (pointsEquiv b T' (a ≫ x) :
        ((algΓ (CommRingCat.of k)).obj T').unop ⊗[k] Matrix m m D) =
    (coefficientEquiv k D ((algΓ (CommRingCat.of k)).obj T).unop
      (pointsEquiv b T x :
        ((algΓ (CommRingCat.of k)).obj T).unop ⊗[k] Matrix m m D)).map
      (Algebra.TensorProduct.map
        ((algΓ (CommRingCat.of k)).map a).unop.hom (AlgHom.id k D))
  erw [FiniteAlgebraUnits.pointsEquiv_naturality b a x]
  exact coefficientEquiv_naturality k D ((algΓ (CommRingCat.of k)).map a).unop.hom _

end MatrixPoints

end Langlands.GroupScheme.FiniteAlgebraUnits
