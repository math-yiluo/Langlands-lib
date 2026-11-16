import Langlands.GroupScheme.ChevalleyIntegral.AmbientProductCell
import Langlands.GroupScheme.Dynamic.GeneralLinearBaseChange
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange

/-! # Restriction of Chevalley cell parameters along a change of base -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence.ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base} (D : ChevalleyData P b)
  [DecidableEq J]

/-- Points of an ordered root parameter scheme are its list coordinates in global sections. -/
def orderedRootPointsEquiv (R : CommRingCat.{u}) (l : List J) (T : Over (Spec R)) :
    (T ⟶ D.orderedRootSpace R l) ≃ ({j : J // j ∈ l} → Γ(T.left, ⊤)) := by
  letI : Algebra R Γ(T.left, ⊤) :=
    inferInstanceAs (Algebra R ((algΓ R).obj T).unop)
  exact {
  toFun x j := (((algΓAlgSpecAdjunction R).homEquiv T
    (op (D.orderedRootAlgebra R l))).symm x).unop.hom (MvPolynomial.X j)
  invFun c := (algΓAlgSpecAdjunction R).homEquiv T _
    (CommAlgCat.ofHom (MvPolynomial.aeval c)).op
  left_inv x := by
    apply ((algΓAlgSpecAdjunction R).homEquiv T _).symm.injective
    simp only [Equiv.symm_apply_apply]
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    apply MvPolynomial.algHom_ext
    intro j
    exact MvPolynomial.aeval_X _ _
  right_inv c := by
    funext j
    simp only [Equiv.symm_apply_apply]
    change (MvPolynomial.aeval c) (MvPolynomial.X j) = c j
    exact MvPolynomial.aeval_X _ _ }

/-- The matrix product at an arbitrary scheme-valued parameter point. -/
theorem pointsEquiv_orderedRootMapOver (R : CommRingCat.{u}) (l : List J)
    (T : Over (Spec R)) (x : T ⟶ D.orderedRootSpace R l) :
    GeneralLinear.pointsEquiv (Fin D.n) R T (x ≫ D.orderedRootMapOver R l) =
      D.opmGL l (fun j => if hj : j ∈ l then D.orderedRootPointsEquiv R l T x ⟨j, hj⟩ else 0) := by
  change T ⟶ (algSpec R).obj (op (D.orderedRootAlgebra R l)) at x
  change GeneralLinear.point
    ((((algΓAlgSpecAdjunction R).homEquiv T _).symm
      (x ≫ (algSpec R).map (CommAlgCat.ofHom (D.orderedRootClassify R l)).op)).unop.hom) = _
  rw [(algΓAlgSpecAdjunction R).homEquiv_naturality_right_symm]
  change GeneralLinear.point
    (((((algΓAlgSpecAdjunction R).homEquiv T _).symm x).unop.hom).comp
      (D.orderedRootClassify R l)) = _
  rw [GeneralLinear.point_comp, orderedRootClassify, GeneralLinear.point_classify, D.opmGL_map]
  congr 1
  funext j
  simp only [orderedRootVariables, Function.comp_apply]
  split_ifs
  · rfl
  · exact map_zero _

variable {R S : CommRingCat.{u}} (a : Spec S ⟶ Spec R)

/-- A matrix point over the new base, regarded over the old base. -/
def matrixRestrict (T : Over (Spec S)) (x : T ⟶ (D.GLR S).X) :
    (Over.map a).obj T ⟶ (D.GLR R).X :=
  baseChangePointsEquiv a (D.GLR R) T
    (x ≫ (GeneralLinear.baseChangeIso (Fin D.n) a).inv.hom.hom)

omit [DecidableEq J] in
@[simp] theorem pointsEquiv_matrixRestrict (T : Over (Spec S)) (x : T ⟶ (D.GLR S).X) :
    GeneralLinear.pointsEquiv (Fin D.n) R ((Over.map a).obj T) (D.matrixRestrict a T x) =
      GeneralLinear.pointsEquiv (Fin D.n) S T x := by
  rw [matrixRestrict, ← GeneralLinear.pointsEquiv_comp_baseChangeIso_hom]
  simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom,
    Category.comp_id]

omit [DecidableEq J] in
@[simp] theorem matrixRestrict_mul (T : Over (Spec S)) (x y : T ⟶ (D.GLR S).X) :
    D.matrixRestrict a T (x * y) = D.matrixRestrict a T x * D.matrixRestrict a T y := by
  simp only [matrixRestrict, MonObj.mul_comp, map_mul]

omit [DecidableEq J] in
@[simp] theorem matrixRestrict_comp {T W : Over (Spec S)} (f : W ⟶ T)
    (x : T ⟶ (D.GLR S).X) :
    D.matrixRestrict a W (f ≫ x) = (Over.map a).map f ≫ D.matrixRestrict a T x := by
  simp only [matrixRestrict, Category.assoc, baseChangePointsEquiv_naturality]

/-- The same list coordinates define a point over the old base. -/
def orderedRootRestrict (l : List J) :
    (Over.map a).obj (D.orderedRootSpace S l) ⟶ D.orderedRootSpace R l :=
  (D.orderedRootPointsEquiv R l _).symm
    (D.orderedRootPointsEquiv S l _ (𝟙 _))

/-- Restricting list coordinates commutes with their ordered matrix product. -/
@[simp] theorem orderedRootRestrict_comp (l : List J) :
    D.orderedRootRestrict a l ≫ D.orderedRootMapOver R l =
      D.matrixRestrict a _ (D.orderedRootMapOver S l) := by
  apply (GeneralLinear.pointsEquiv (Fin D.n) R _).injective
  rw [D.pointsEquiv_orderedRootMapOver, orderedRootRestrict, Equiv.apply_symm_apply,
    pointsEquiv_matrixRestrict]
  simpa only [Category.id_comp] using
    (D.pointsEquiv_orderedRootMapOver S l _ (𝟙 _)).symm

/-- The full-lattice character point, regarded over the old base. -/
def torusRestrict (_D : ChevalleyData P b) :
    (Over.map a).obj (TR (X := X) S).toGrp.X ⟶ (TR (X := X) R).toGrp.X :=
  baseChangePointsEquiv a (TR (X := X) R).toGrp _
    (Diagonalizable.baseChangeIso a X).inv.hom.hom

omit [DecidableEq J] in
/-- Restricting the full character point commutes with the torus matrix representation. -/
@[simp] theorem torusRestrict_comp :
    D.torusRestrict a ≫ (D.torusToGLOver R).hom.hom =
      D.matrixRestrict a _ (D.torusToGLOver S).hom.hom := by
  apply (GeneralLinear.pointsEquiv (Fin D.n) R _).injective
  rw [D.pointsEquiv_torusToGLOver, pointsEquiv_matrixRestrict]
  have h := D.pointsEquiv_torusToGLOver S (TR (X := X) S).toGrp.X (𝟙 _)
  rw [Category.id_comp] at h
  rw [h]
  congr 1
  exact (Diagonalizable.baseChangeCharacterPointsEquiv_baseChangeIso_inv a X _ (𝟙 _))

/-- Restriction of all three factors of an ordered matrix cell. -/
def orderedCellRestrict (lm lp : List J) :
    (Over.map a).obj (D.orderedCellSpace S lm lp) ⟶ D.orderedCellSpace R lm lp :=
  lift ((Over.map a).map (fst _ _) ≫ D.neg.orderedRootRestrict a lm)
    (lift ((Over.map a).map (snd _ _ ≫ fst _ _) ≫ D.torusRestrict a)
      ((Over.map a).map (snd _ _ ≫ snd _ _) ≫ D.orderedRootRestrict a lp))

/-- Restriction of the ordered parameters preserves the actual matrix triple product. -/
@[simp] theorem orderedCellRestrict_comp (lm lp : List J) :
    D.orderedCellRestrict a lm lp ≫ D.orderedCellMap R lm lp =
      D.matrixRestrict a _ (D.orderedCellMap S lm lp) := by
  simp only [orderedCellMap, MonObj.comp_mul, orderedCellRestrict,
    lift_fst_assoc, lift_snd_assoc, Category.assoc,
    orderedRootRestrict_comp, torusRestrict_comp, matrixRestrict_mul,
    matrixRestrict_comp, Functor.map_comp, Category.assoc]
  rfl

end Langlands.GroupScheme.SplitExistence.ChevalleyData
