import Langlands.GroupScheme.Rational.GeneralLinearCharacterAlgebra
import Langlands.GroupScheme.Rational.GeneralLinearCharacterMatrices
import Langlands.GroupScheme.Dynamic.GeneralLinear
import Langlands.GroupScheme.Torus.GmEndomorphismsProof

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable (n : Type) [Fintype n] [DecidableEq n] (R : CommRingCat.{u})

/-- The cocharacter which changes a single diagonal entry. -/
def coordinateDiagonalHom (i : n) : (Gm (Spec R)).toGrp ⟶ groupScheme n R :=
  diagonalCocharacter n R (fun j => if j = i then 1 else 0)

variable {n R}

theorem diagonalUnits_coordinate {A : Type*} [CommRing A] (i : n) (a : Aˣ) :
    diagonalUnits A (fun j => if j = i then 1 else 0) a =
      coordinateDiagonalUnits A i a := by
  apply Units.ext
  ext j k
  simp only [coe_diagonalUnits, coordinateDiagonalUnits_apply, diagonalMatrixUnits_val,
    Matrix.diagonal_apply, Pi.mulSingle_apply]
  split_ifs <;> simp_all

theorem pointsEquiv_coordinateDiagonalHom (i : n) {T : Over (Spec R)}
    (x : T ⟶ (Gm (Spec R)).X) :
    pointsEquiv n R T (x ≫ (coordinateDiagonalHom n R i).hom.hom) =
      coordinateDiagonalUnits Γ(T.left, ⊤) i (Gm.pointsEquiv (Spec R) T x) := by
  rw [coordinateDiagonalHom, pointsEquiv_diagonalCocharacter, diagonalUnits_coordinate]

theorem map_coordinateDiagonalUnits {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (i : n) (a : Aˣ) :
    Matrix.GeneralLinearGroup.map f (coordinateDiagonalUnits A i a) =
      coordinateDiagonalUnits B i (Units.map f.toMonoidHom a) := by
  ext j k
  simp only [Matrix.GeneralLinearGroup.map_apply, coordinateDiagonalUnits_apply,
    diagonalMatrixUnits_val, Matrix.diagonal_apply, Pi.mulSingle_apply]
  split_ifs <;> simp_all

theorem gm_affinePointsEquiv_algSpec_naturality {A B : CommAlgCat.{u} R}
    (f : A ⟶ B) (x : (algSpec R).obj (op A) ⟶ (Gm (Spec R)).X) :
    Gm.affinePointsEquiv ((algSpec R).obj (op B)).hom ((algSpec R).map f.op ≫ x) =
      Units.map f.hom.toRingHom.toMonoidHom
        (Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom x) := by
  apply Units.ext
  rw [Gm.affinePointsEquiv_val, Gm.pointsEquiv_naturality]
  change ((Spec.map (CommRingCat.ofHom f.hom.toRingHom)).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom) _ =
    f.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).hom _)
  rw [Scheme.ΓSpecIso_naturality]
  rfl

/-- An actual scheme character evaluated on matrices over a test algebra. -/
def characterOnAffineMatrices (φ : groupScheme n R ⟶ (Gm (Spec R)).toGrp)
    (A : CommAlgCat.{u} R) : GL n A →* Aˣ :=
  (Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom).toMonoidHom.comp
    (((pointsMap φ).app (op ((algSpec R).obj (op A)))).hom.comp
      (affinePointsEquiv n R A).symm.toMonoidHom)

@[simp] theorem characterOnAffineMatrices_apply
    (φ : groupScheme n R ⟶ (Gm (Spec R)).toGrp) (A : CommAlgCat.{u} R) (g : GL n A) :
    characterOnAffineMatrices φ A g =
      Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom
        ((affinePointsEquiv n R A).symm g ≫ φ.hom.hom) := rfl

theorem characterOnAffineMatrices_naturality
    (φ : groupScheme n R ⟶ (Gm (Spec R)).toGrp) {A B : CommAlgCat.{u} R}
    (f : A ⟶ B) (g : GL n A) :
    characterOnAffineMatrices φ B (Matrix.GeneralLinearGroup.map f.hom.toRingHom g) =
      Units.map f.hom.toRingHom.toMonoidHom (characterOnAffineMatrices φ A g) := by
  have hx : (affinePointsEquiv n R B).symm (Matrix.GeneralLinearGroup.map f.hom.toRingHom g) =
      (algSpec R).map f.op ≫ (affinePointsEquiv n R A).symm g := by
    apply (affinePointsEquiv n R B).injective
    rw [MulEquiv.apply_symm_apply, affinePointsEquiv_naturality,
      MulEquiv.apply_symm_apply]
  rw [characterOnAffineMatrices_apply, hx, Category.assoc,
    gm_affinePointsEquiv_algSpec_naturality]
  rfl

theorem affinePointsEquiv_coordinateDiagonalHom (i : n) (A : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op A) ⟶ (Gm (Spec R)).X) :
    affinePointsEquiv n R A (x ≫ (coordinateDiagonalHom n R i).hom.hom) =
      coordinateDiagonalUnits A i (Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom x) := by
  apply Units.map_injective
    (f := ((Corepresented.affineSectionsIso A).inv.hom.toRingHom.mapMatrix).toMonoidHom)
    (Matrix.map_injective (Corepresented.affineSectionsAlgEquiv A).symm.injective)
  change Matrix.GeneralLinearGroup.map (Corepresented.affineSectionsIso A).inv.hom.toRingHom
      (affinePointsEquiv n R A (x ≫ (coordinateDiagonalHom n R i).hom.hom)) =
    Matrix.GeneralLinearGroup.map (Corepresented.affineSectionsIso A).inv.hom.toRingHom
      (coordinateDiagonalUnits A i (Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom x))
  rw [← pointsEquiv_eq_affinePointsEquiv, pointsEquiv_coordinateDiagonalHom,
    map_coordinateDiagonalUnits]
  congr 1
  apply Units.ext
  change (Gm.pointsEquiv (Spec R) ((algSpec R).obj (op A)) x).val =
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv
      ((Scheme.ΓSpecIso (CommRingCat.of A)).hom _)
  simp
  rfl

theorem characterOnAffineMatrices_coordinate
    (φ : groupScheme n R ⟶ (Gm (Spec R)).toGrp) (i : n) (m : ℤ)
    (hm : coordinateDiagonalHom n R i ≫ φ = multiplication (Gm (Spec R)).toGrp m)
    (A : CommAlgCat.{u} R) (a : Aˣ) :
    characterOnAffineMatrices φ A (coordinateDiagonalUnits A i a) = a ^ m := by
  let x := (Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom).symm a
  have hx : (affinePointsEquiv n R A).symm (coordinateDiagonalUnits A i a) =
      x ≫ (coordinateDiagonalHom n R i).hom.hom := by
    apply (affinePointsEquiv n R A).injective
    rw [MulEquiv.apply_symm_apply, affinePointsEquiv_coordinateDiagonalHom]
    simp [x]
  rw [characterOnAffineMatrices_apply, hx, Category.assoc]
  change Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom
    (x ≫ (coordinateDiagonalHom n R i ≫ φ).hom.hom) = _
  rw [hm, points_multiplication, map_zpow]
  exact congrArg (fun z : Aˣ => z ^ m)
    ((Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom).apply_symm_apply a)

end Langlands.GroupScheme.GeneralLinear
