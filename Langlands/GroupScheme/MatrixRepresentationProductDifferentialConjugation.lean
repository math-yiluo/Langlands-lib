import Langlands.GroupScheme.MatrixRepresentationProductDifferential
import Langlands.GroupScheme.MatrixRepresentationDifferentialConjugation

/-! # Matrix evaluation and conjugation for actual finite-product scheme representations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.GeneralLinearProductDualNumber

open GeneralLinear

variable {I : Type u} [Finite I]
variable {n : I → Type} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
variable {R : CommRingCat.{u}}
variable {S T : Type u} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

/-- Actual affine product points in the full family of invertible matrix coordinates. -/
def affineMatrixEquiv (S : Type u) [CommRing S] [Algebra R S] :
    AffinePoints n R S ≃* ∀ i, GL (n i) S :=
  (affinePointsPiEquiv S).trans
    (MulEquiv.piCongrRight fun i => affinePointsEquiv (n i) R (CommAlgCat.of R S))

@[simp] theorem affineMatrixEquiv_apply (x : AffinePoints n R S) (i : I) :
    affineMatrixEquiv S x i =
      affinePointsEquiv (n i) R (CommAlgCat.of R S) (x ≫ proj n R i) := rfl

/-- Actual coefficient change is entrywise coefficient change in every matrix factor. -/
theorem affineMatrixEquiv_naturality (f : S →ₐ[R] T) (x : AffinePoints n R S) (i : I) :
    affineMatrixEquiv T (affineMap f x) i =
      Matrix.GeneralLinearGroup.map f.toRingHom (affineMatrixEquiv S x i) := by
  change affinePointsEquiv (n i) R (CommAlgCat.of R T)
      (affinePointsPiEquiv T (affineMap f x) i) = _
  rw [affinePointsPiEquiv_affineMap]
  exact DualNumber.affineMap_matrix f _

/-- All components of the actual dual-number point have their published matrix units. -/
@[simp] theorem affineMatrixEquiv_pointUnit (X : ∀ i, Matrix (n i) (n i) S) :
    affineMatrixEquiv (DualNumber S) (pointUnit (R := R) X) =
      fun i => DualNumber.matrixUnit (X i) := by
  funext i
  exact pointUnit_matrix X i

/-- The inverse matrix coordinates recover the actual product dual-number point. -/
@[simp] theorem affineMatrixEquiv_symm_matrixUnit (X : ∀ i, Matrix (n i) (n i) S) :
    (affineMatrixEquiv (n := n) (R := R) (DualNumber S)).symm
        (fun i => DualNumber.matrixUnit (X i)) = pointUnit X := by
  apply (affineMatrixEquiv (n := n) (R := R) (DualNumber S)).injective
  rw [MulEquiv.apply_symm_apply, affineMatrixEquiv_pointUnit]

end Langlands.GroupScheme.GeneralLinearProductDualNumber

namespace Langlands.GroupScheme.MatrixRepresentation

open GeneralLinear GeneralLinearProductDualNumber

variable {I : Type u} [Finite I]
variable {n : I → Type} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
variable {R : CommRingCat.{u}}
variable {m : Type} [Fintype m] [DecidableEq m]
variable {S T : Type u} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

/-- Evaluate the actual product-source scheme morphism on invertible matrix families. -/
def productMatrixPointsHom (ρ : MatrixRepresentation (groupScheme n R) m) (S : Type u)
    [CommRing S] [Algebra R S] : (∀ i, GL (n i) S) →* GL m S :=
  (ρ.affineMatrix (CommAlgCat.of R S)).comp
    (affineMatrixEquiv (n := n) (R := R) S).symm.toMonoidHom

@[simp] theorem productMatrixPointsHom_apply
    (ρ : MatrixRepresentation (groupScheme n R) m) (g : ∀ i, GL (n i) S) :
    ρ.productMatrixPointsHom S g =
      ρ.affineMatrix (CommAlgCat.of R S)
        ((affineMatrixEquiv (n := n) (R := R) S).symm g) := rfl

/-- The actual evaluated homomorphism commutes with arbitrary test-algebra maps. -/
theorem productMatrixPointsHom_naturality (ρ : MatrixRepresentation (groupScheme n R) m)
    (f : S →ₐ[R] T) (g : ∀ i, GL (n i) S) :
    ρ.productMatrixPointsHom T (fun i => Matrix.GeneralLinearGroup.map f.toRingHom (g i)) =
      Matrix.GeneralLinearGroup.map f.toRingHom (ρ.productMatrixPointsHom S g) := by
  have hp :
      (affineMatrixEquiv (n := n) (R := R) T).symm
          (fun i => Matrix.GeneralLinearGroup.map f.toRingHom (g i)) =
        affineMap f ((affineMatrixEquiv (n := n) (R := R) S).symm g) := by
    apply (affineMatrixEquiv (n := n) (R := R) T).injective
    rw [MulEquiv.apply_symm_apply]
    funext i
    rw [affineMatrixEquiv_naturality, MulEquiv.apply_symm_apply]
  rw [productMatrixPointsHom_apply, hp]
  exact ρ.affineMatrix_naturality (CommAlgCat.ofHom f) _

/-- The product differential is the first-order part of the actual matrix homomorphism. -/
theorem productMatrixPointsHom_matrixUnit (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : ∀ i, Matrix (n i) (n i) S) :
    ρ.productMatrixPointsHom (DualNumber S) (fun i => DualNumber.matrixUnit (X i)) =
      DualNumber.matrixUnit (ρ.productDifferential S X) := by
  rw [productMatrixPointsHom_apply, affineMatrixEquiv_symm_matrixUnit]
  exact ρ.productDifferential_affineMatrix X

/-- The constructed differential intertwines full componentwise matrix conjugation. -/
theorem productDifferential_conjugate (ρ : MatrixRepresentation (groupScheme n R) m)
    (g : ∀ i, GL (n i) S) (X : ∀ i, Matrix (n i) (n i) S) :
    ρ.productDifferential S
        (fun i => (g i : Matrix (n i) (n i) S) * X i *
          (((g i)⁻¹ : GL (n i) S) : Matrix (n i) (n i) S)) =
      (ρ.productMatrixPointsHom S g : Matrix m m S) * ρ.productDifferential S X *
        (((ρ.productMatrixPointsHom S g)⁻¹ : GL m S) : Matrix m m S) := by
  have hinl : (TrivSqZeroExt.inlAlgHom R S S).toRingHom =
      TrivSqZeroExt.inlHom S S := by
    ext s <;> rfl
  have hc := ρ.productMatrixPointsHom_naturality (TrivSqZeroExt.inlAlgHom R S S) g
  rw [hinl] at hc
  have hs :
      (fun i => DualNumber.matrixUnit
        ((g i : Matrix (n i) (n i) S) * X i *
          (((g i)⁻¹ : GL (n i) S) : Matrix (n i) (n i) S))) =
      (fun i => Matrix.GeneralLinearGroup.map (TrivSqZeroExt.inlHom S S) (g i)) *
        (fun i => DualNumber.matrixUnit (X i)) *
        (fun i => Matrix.GeneralLinearGroup.map (TrivSqZeroExt.inlHom S S) (g i))⁻¹ := by
    funext i
    exact DualNumber.matrixUnit_conjugate (g i) (X i)
  have h := congrArg (ρ.productMatrixPointsHom (DualNumber S)) hs
  rw [productMatrixPointsHom_matrixUnit,
    map_mul (ρ.productMatrixPointsHom (DualNumber S)),
    map_mul (ρ.productMatrixPointsHom (DualNumber S)),
    map_inv (ρ.productMatrixPointsHom (DualNumber S)),
    productMatrixPointsHom_matrixUnit, hc,
    ← DualNumber.matrixUnit_conjugate] at h
  simpa only [DualNumber.coefficients_matrixUnit] using congrArg DualNumber.coefficients h

end Langlands.GroupScheme.MatrixRepresentation
