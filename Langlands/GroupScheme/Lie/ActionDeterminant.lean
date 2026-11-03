import Langlands.GroupScheme.Lie.FiniteAction

/-! # Determinant character of an actual finite Lie action -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme
namespace AutomorphicAction

variable {R : CommRingCat.{u}} {H U : GroupScheme (Spec R)}
  [IsAffineHom U.X.hom] (a : AutomorphicAction H U) {d : ℕ}
  (c : Lie.FiniteCoordinates U d)

/-- The coordinate-matrix determinant is the determinant on the actual Lie module. -/
theorem coordinateMatrix_det (A : CommAlgCat.{u} R) (h : H.affinePoints A) :
    Matrix.GeneralLinearGroup.det (a.coordinateMatrix c A h) =
      LinearEquiv.det (a.differential h) := by
  have hlin : (a.coordinateAction c A h).toLinearMap =
      Matrix.toLin' (a.coordinateMatrix c A h : Matrix (Fin d) (Fin d) A) := by
    apply LinearMap.ext
    intro v
    exact (a.coordinateMatrix_mulVec c A h v).symm
  have hc : Matrix.GeneralLinearGroup.det (a.coordinateMatrix c A h) =
      LinearEquiv.det (a.coordinateAction c A h) := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, LinearEquiv.coe_det,
      hlin, LinearMap.det_toLin']
  exact hc.trans (LinearEquiv.det_conj (a.differential h) (c.equiv A))

include c in
/-- Determinants of the actual differentials commute with every algebra map. -/
theorem differential_det_naturality {A B : CommAlgCat.{u} R} (f : A ⟶ B)
    (h : H.affinePoints A) :
    LinearEquiv.det (a.differential (H.affinePointMap f h)) =
      Units.map f.hom.toRingHom.toMonoidHom (LinearEquiv.det (a.differential h)) := by
  rw [← a.coordinateMatrix_det c, a.coordinateMatrix_naturality c,
    Matrix.GeneralLinearGroup.map_det, a.coordinateMatrix_det c]
  rfl


variable [IsAffine H.X.left]

/-- Compose the constructed algebraic differential representation with determinant. -/
def determinantCharacter : rationalCharacters H :=
  characterRestrict (a.finiteRepresentation c) (GeneralLinear.determinantCharacter (Fin d) R)

/-- On every scheme test, evaluation is the determinant of the actual representation. -/
theorem determinantCharacter_eval (T : Over (Spec R)) (h : T ⟶ H.X) :
    characterEval (a.determinantCharacter c) T h =
      Matrix.GeneralLinearGroup.det ((a.finiteRepresentation c).pointMatrix T h) := by
  rw [determinantCharacter, characterEval_characterRestrict,
    GeneralLinear.characterEval_determinantCharacter]
  rfl

/-- On every affine test the value is the actual Lie determinant, transported to sections. -/
theorem determinantCharacter_eval_affine (A : CommAlgCat.{u} R) (h : H.affinePoints A) :
    characterEval (a.determinantCharacter c) ((algSpec R).obj (op A)) h =
      Units.map (Corepresented.affineSectionsIso A).inv.hom.toRingHom.toMonoidHom
        (LinearEquiv.det (a.differential h)) := by
  rw [determinantCharacter_eval, MatrixRepresentation.pointMatrix_eq_affineMatrix,
    finiteRepresentation_affineMatrix]
  exact (Matrix.GeneralLinearGroup.map_det _ _).trans
    (congrArg
      (Units.map (Corepresented.affineSectionsIso A).inv.hom.toRingHom.toMonoidHom)
      (a.coordinateMatrix_det c A h))

/-- Reading the actual Gm-valued morphism in affine coordinates gives exactly det(d a). -/
theorem determinantCharacter_affinePoints (A : CommAlgCat.{u} R) (h : H.affinePoints A) :
    Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom
        (h ≫ (a.determinantCharacter c).toMul.hom.hom) =
      LinearEquiv.det (a.differential h) := by
  apply Units.ext
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    (characterEval (a.determinantCharacter c) ((algSpec R).obj (op A)) h).val = _
  rw [determinantCharacter_eval_affine]
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (LinearEquiv.det (a.differential h)).val) = _
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id _


end AutomorphicAction
end Langlands.GroupScheme
