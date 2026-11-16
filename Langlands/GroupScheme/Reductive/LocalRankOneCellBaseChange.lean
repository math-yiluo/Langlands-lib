import Langlands.GroupScheme.Reductive.LocalRankOneCellData

/-! # Coordinate-preserving base change of actual rank-one cells -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.LocalRankOneCell

open LocalSplitCell LocalSplitRootBaseChange

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))}
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (a : I → ℤ) (xm xp : Ga R ⟶ G)

/-- An actual open triple cell remains open after arbitrary coefficient
base change, in the standard additive and torus coordinates. -/
theorem isOpenImmersion_baseChange
    (hopen : IsOpenImmersion (Dynamic.tripleCellMultiplication xm i xp).left)
    (A : Type u) [CommRing A] [Algebra R A] :
    IsOpenImmersion (Dynamic.tripleCellMultiplication (baseChangeRoot A xm)
      (splitTorus.baseChangeHom (K := A) G I i) (baseChangeRoot A xp)).left := by
  let b := algebraBaseMap R A
  let m := Dynamic.tripleCellMultiplication xm i xp
  have hpull : IsOpenImmersion ((Over.pullback b).map m).left := by
    have h := Scheme.pullback_map_isOpenImmersion
      ((Ga R).X ⊗ ((splitTorus (Spec (CommRingCat.of R)) I).X ⊗ (Ga R).X)).hom b
      G.X.hom b m.left (𝟙 _) (𝟙 _)
      (by simp) (by simp)
    simpa only [Over.pullback_map_left, Limits.pullback.map, Category.comp_id] using h
  let e := standardTripleBaseChangeIso (R := R) A I
  have he : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have hcomp : IsOpenImmersion
      (e.hom.left ≫ ((Over.pullback b).map m).left) := inferInstance
  change IsOpenImmersion (e.hom ≫ (Over.pullback b).map m).left at hcomp
  rw [standardTripleBaseChangeIso_hom_comp] at hcomp
  exact hcomp

/-- Base change of an actual opposite-root cell, retaining the fixed
exponent and standard coordinates. -/
def baseChangeCellData
    (hm : IsRootParametrization i (-a) xm) (hp : IsRootParametrization i a xp)
    (hopen : IsOpenImmersion (Dynamic.tripleCellMultiplication xm i xp).left)
    (A : Type u) [CommRing A] [Algebra R A] : RingRootCell.CellData A where
  G := (GroupScheme.baseChange (algebraBaseMap R A)).obj G
  T := splitTorus.commGroupScheme _ I
  i := splitTorus.baseChangeHom (K := A) G I i
  xp := baseChangeRoot A xp
  xm := baseChangeRoot A xm
  α := splitTorus.exponentCharacter _ I a
  hxp := (isRootParametrization_baseChangeRoot A i a xp hp).equivariant_point
  hxm := by
    have hneg : splitTorus.exponentCharacter (Spec (CommRingCat.of A)) I (-a) =
        -splitTorus.exponentCharacter (Spec (CommRingCat.of A)) I a :=
      (splitTorus.exponentCharacterLinear _ I).map_neg a
    simpa only [hneg] using
      (isRootParametrization_baseChangeRoot A i (-a) xm hm).equivariant_point
  open_cell := isOpenImmersion_baseChange i xm xp hopen A

/-- Cell coordinates on the actual base change give the same three-factor
point over the original base. -/
theorem baseChangePointsEquiv_cellPt
    (hm : IsRootParametrization i (-a) xm) (hp : IsRootParametrization i a xp)
    (hopen : IsOpenImmersion (Dynamic.tripleCellMultiplication xm i xp).left)
    (A : Type u) [CommRing A] [Algebra R A]
    {Z : Over (Spec (CommRingCat.of A))}
    (y : Γ(Z.left, ⊤)) (t : Z ⟶ (splitTorus (Spec (CommRingCat.of A)) I).X)
    (x : Γ(Z.left, ⊤)) :
    GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z
      ((baseChangeCellData i a xm xp hm hp hopen A).cellPt y t x) =
    rootPoint xm ((Over.map (algebraBaseMap R A)).obj Z) y *
      ((GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) (splitTorus _ I) Z
        (t ≫ (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv.hom.hom) ≫ i.hom.hom) *
        rootPoint xp ((Over.map (algebraBaseMap R A)).obj Z) x) := by
  change GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z
    (rootPoint (baseChangeRoot A xm) Z y *
      ((t ≫ (splitTorus.baseChangeHom (K := A) G I i).hom.hom) *
        rootPoint (baseChangeRoot A xp) Z x)) = _
  rw [map_mul, map_mul, baseChangePointsEquiv_rootPoint,
    baseChangePointsEquiv_rootPoint, baseChangePointsEquiv_torus]

end Langlands.GroupScheme.LocalRankOneCell
