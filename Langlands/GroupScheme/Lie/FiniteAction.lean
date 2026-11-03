import Langlands.GroupScheme.Lie.ActionDifferential
import Langlands.GroupScheme.AffineCorepresented
import Langlands.GroupScheme.MatrixRepresentation
import Langlands.GroupScheme.Rational.Characters
import Mathlib.LinearAlgebra.Determinant

/-! # Finite coordinates for the actual Lie action -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

namespace Lie

variable {R : CommRingCat.{u}} (U : GroupScheme (Spec R)) [IsAffineHom U.X.hom]

/-- Finite coordinates on the actual Lie kernel, compatible with every algebra map.
No representation or character is part of this datum. -/
structure FiniteCoordinates (d : ℕ) where
  equiv : ∀ (A : CommAlgCat.{u} R),
    Additive (lieKernel U A) ≃ₗ[A] (Fin d → A)
  naturality : ∀ {A B : CommAlgCat.{u} R} (f : A ⟶ B)
    (x : Additive (lieKernel U A)),
    equiv B (lieKernelMapLinear U f.hom x) = fun i => f.hom (equiv A x i)

end Lie

namespace AffineCoordinates

variable {R : CommRingCat.{u}} (H : GroupScheme (Spec R)) [IsAffine H.X.left]

/-- The chosen corepresentation recovers the actual affine points of `H`. -/
def actualPointsEquiv (A : CommAlgCat.{u} R) :
    (functor H).obj A ≃* H.affinePoints A :=
  (Corepresented.affinePointsEquiv _ (corepresentation H) A).symm.trans
    { toFun := fun x => x ≫ (groupSchemeIso H).hom.hom.hom
      invFun := fun x => x ≫ (groupSchemeIso H).inv.hom.hom
      left_inv := fun x => by
        dsimp only
        rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom,
          Category.comp_id]
      right_inv := fun x => by
        dsimp only
        rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom,
          Category.comp_id]
      map_mul' := fun x y => MonObj.mul_comp x y _ }

/-- Corepresented coordinates recover actual coefficient change. -/
theorem actualPointsEquiv_naturality {A B : CommAlgCat.{u} R} (f : A ⟶ B)
    (x : (functor H).obj A) :
    actualPointsEquiv H B ((functor H).map f x) =
      H.affinePointMap f (actualPointsEquiv H A x) := by
  have he :
      (Corepresented.affinePointsEquiv _ (corepresentation H) B).symm
          ((functor H).map f x) =
        (algSpec R).map f.op ≫
          (Corepresented.affinePointsEquiv _ (corepresentation H) A).symm x := by
    apply (Corepresented.affinePointsEquiv _ (corepresentation H) B).injective
    rw [MulEquiv.apply_symm_apply, Corepresented.affinePointsEquiv_naturality,
      MulEquiv.apply_symm_apply]
  exact (congrArg (fun z => z ≫ (groupSchemeIso H).hom.hom.hom) he).trans
    (Category.assoc _ _ _)

variable {n : Type} [Fintype n] [DecidableEq n]
  (α : ∀ A : CommAlgCat.{u} R, H.affinePoints A →* GL n A)
  (hα : ∀ {A B : CommAlgCat.{u} R} (f : A ⟶ B) (h : H.affinePoints A),
    α B (H.affinePointMap f h) = Matrix.GeneralLinearGroup.map f.hom.toRingHom (α A h))

/-- Natural affine matrix homomorphisms induce a natural transformation of the
chosen corepresented algebra-point functors. -/
def matrixNaturalTransformation : functor H ⟶ GeneralLinear.functor n R where
  app A := GrpCat.ofHom ((α A).comp (actualPointsEquiv H A).toMonoidHom)
  naturality {A B} f := by
    ext x
    exact (congrArg (α B) (actualPointsEquiv_naturality H f x)).trans (hα f _)

/-- Algebraicity follows from naturality on all test algebras and affineness of
the actual source, by corepresented Yoneda. -/
def matrixRepresentationOfAffinePoints : MatrixRepresentation H n :=
  (groupSchemeIso H).inv ≫
    Corepresented.groupSchemeMap (corepresentation H) (GeneralLinear.corepresentableBy n R)
      (matrixNaturalTransformation H α hα)

/-- The algebraic representation recovers the specified matrices on every algebra. -/
theorem matrixRepresentationOfAffinePoints_affineMatrix (A : CommAlgCat.{u} R)
    (h : H.affinePoints A) :
    (matrixRepresentationOfAffinePoints H α hα).affineMatrix A h = α A h := by
  rw [MatrixRepresentation.affineMatrix_apply]
  change GeneralLinear.affinePointsEquiv n R A
    (h ≫ ((groupSchemeIso H).inv ≫
      Corepresented.groupSchemeMap (corepresentation H)
        (GeneralLinear.corepresentableBy n R)
        (matrixNaturalTransformation H α hα)).hom.hom) = _
  rw [Grp.comp_hom_hom, ← Category.assoc]
  refine (Corepresented.groupSchemeMap_affinePoints (corepresentation H)
    (GeneralLinear.corepresentableBy n R) (matrixNaturalTransformation H α hα)
    (h ≫ (groupSchemeIso H).inv.hom.hom)).trans ?_
  change α A (actualPointsEquiv H A
    (Corepresented.affinePointsEquiv _ (corepresentation H) A
      (h ≫ (groupSchemeIso H).inv.hom.hom))) = α A h
  congr 1
  change (Corepresented.affinePointsEquiv _ (corepresentation H) A).symm
    (Corepresented.affinePointsEquiv _ (corepresentation H) A
      (h ≫ (groupSchemeIso H).inv.hom.hom)) ≫ (groupSchemeIso H).hom.hom.hom = h
  rw [MulEquiv.symm_apply_apply, Category.assoc, ← Grp.comp_hom_hom,
    Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

end AffineCoordinates

namespace AutomorphicAction

variable {R : CommRingCat.{u}} {H U : GroupScheme (Spec R)}
  [IsAffineHom U.X.hom] (a : AutomorphicAction H U) {d : ℕ}
  (c : Lie.FiniteCoordinates U d)

/-- The actual differential in finite coordinates; it is constructed from the
given action, rather than supplied with the coordinate datum. -/
def coordinateAction (A : CommAlgCat.{u} R) :
    H.affinePoints A →* ((Fin d → A) ≃ₗ[A] (Fin d → A)) where
  toFun h := (c.equiv A).symm.trans ((a.differential h).trans (c.equiv A))
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change c.equiv A (a.differentialRepresentation A 1 ((c.equiv A).symm v)) = v
    rw [map_one]
    exact (c.equiv A).apply_symm_apply v
  map_mul' h h' := by
    apply LinearEquiv.ext
    intro v
    change c.equiv A (a.differentialRepresentation A (h * h') ((c.equiv A).symm v)) =
      c.equiv A (a.differential h
        ((c.equiv A).symm (c.equiv A (a.differential h' ((c.equiv A).symm v)))))
    rw [map_mul, LinearEquiv.symm_apply_apply]
    rfl

/-- Coefficient change intertwines the differential in the chosen coordinates. -/
theorem coordinateAction_naturality {A B : CommAlgCat.{u} R} (f : A ⟶ B)
    (h : H.affinePoints A) (v : Fin d → A) :
    a.coordinateAction c B (H.affinePointMap f h) (fun i => f.hom (v i)) =
      fun i => f.hom (a.coordinateAction c A h v i) := by
  have hv : (c.equiv B).symm (fun i => f.hom (v i)) =
      lieKernelMapLinear U f.hom ((c.equiv A).symm v) := by
    apply (c.equiv B).injective
    rw [LinearEquiv.apply_symm_apply, c.naturality, LinearEquiv.apply_symm_apply]
  change c.equiv B (a.differential (Lie.affineMap H f.hom h)
    ((c.equiv B).symm (fun i => f.hom (v i)))) = _
  rw [hv, ← a.differential_naturality, c.naturality]
  rfl

/-- Invertible coordinate matrices of the actual differential. -/
def coordinateMatrix (A : CommAlgCat.{u} R) : H.affinePoints A →* GL (Fin d) A :=
  ((Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv A (Fin d → A))).symm.toMonoidHom).comp
    (a.coordinateAction c A)

/-- These matrices act by the actual differential in the chosen coordinates. -/
theorem coordinateMatrix_mulVec (A : CommAlgCat.{u} R) (h : H.affinePoints A)
    (v : Fin d → A) :
    (a.coordinateMatrix c A h : Matrix (Fin d) (Fin d) A) *ᵥ v =
      a.coordinateAction c A h v := by
  exact congrArg (fun e : (Fin d → A) ≃ₗ[A] (Fin d → A) => e v)
    ((Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv A (Fin d → A))).apply_symm_apply
        (a.coordinateAction c A h))

/-- The coordinate matrices are natural under every test-algebra map. -/
theorem coordinateMatrix_naturality {A B : CommAlgCat.{u} R} (f : A ⟶ B)
    (h : H.affinePoints A) :
    a.coordinateMatrix c B (H.affinePointMap f h) =
      Matrix.GeneralLinearGroup.map f.hom.toRingHom (a.coordinateMatrix c A h) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have hv : (fun l : Fin d => f.hom ((Pi.single j (1 : A) : Fin d → A) l)) =
      Pi.single j (1 : B) := by
    funext l
    by_cases hl : l = j <;> simp [hl]
  have he := a.coordinateAction_naturality c f h (Pi.single j (1 : A))
  rw [hv, ← coordinateMatrix_mulVec, ← coordinateMatrix_mulVec,
    Matrix.mulVec_single_one, Matrix.mulVec_single_one] at he
  exact congrFun he i

variable [IsAffine H.X.left]

/-- The finite-coordinate differential is an actual algebraic representation. -/
def finiteRepresentation : MatrixRepresentation H (Fin d) :=
  AffineCoordinates.matrixRepresentationOfAffinePoints H (a.coordinateMatrix c)
    (a.coordinateMatrix_naturality c)

/-- On every test algebra the representation has the constructed differential matrices. -/
theorem finiteRepresentation_affineMatrix (A : CommAlgCat.{u} R) (h : H.affinePoints A) :
    (a.finiteRepresentation c).affineMatrix A h = a.coordinateMatrix c A h :=
  AffineCoordinates.matrixRepresentationOfAffinePoints_affineMatrix _ _ _ A h

/-- The resulting algebraic action recovers the differential on the actual Lie module. -/
theorem finiteRepresentation_affineAction (A : CommAlgCat.{u} R) (h : H.affinePoints A)
    (x : Additive (lieKernel U A)) :
    (a.finiteRepresentation c).affineAction A h (c.equiv A x) =
      c.equiv A (a.differential h x) := by
  rw [MatrixRepresentation.affineAction_apply, finiteRepresentation_affineMatrix,
    coordinateMatrix_mulVec]
  change c.equiv A (a.differential h ((c.equiv A).symm (c.equiv A x))) = _
  rw [LinearEquiv.symm_apply_apply]

end AutomorphicAction
end Langlands.GroupScheme
