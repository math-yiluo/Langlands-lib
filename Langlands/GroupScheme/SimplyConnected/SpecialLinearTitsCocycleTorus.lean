import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleStatement
import Langlands.GroupScheme.SpecialLinearTorus
import Langlands.GroupScheme.SpecialLinearBaseChange
import Langlands.GroupScheme.LocalGroupIsoBaseChangeEquivalence

/-! # Diagonal weights and split-torus transport over a field extension -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SpecialLinear

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The character giving the `i`-th diagonal entry of the standard torus. -/
def diagonalWeight (p : n) (S : Scheme.{u}) (i : n) :
    characterLattice (splitTorus.commGroupScheme S (ULift.{u} (OffPivot p))) :=
  ∑ c : ULift.{u} (OffPivot p), weightCoord p i c.down •
    splitTorus.proj S (ULift.{u} (OffPivot p)) c

/-- Diagonal weights evaluate to the published product of coordinate units. -/
theorem pointsEquiv_diagonalWeight (p : n) (S : Scheme.{u}) (i : n)
    {Z : Over S} (s : Z ⟶ (splitTorus S (ULift.{u} (OffPivot p))).X) :
    Gm.pointsEquiv S Z (s ≫ (CommGroupScheme.groupHom (diagonalWeight p S i)).hom.hom) =
      torusWeights p (splitTorus.pointsEquiv (ULift.{u} (OffPivot p)) Z s) i := by
  rw [diagonalWeight]
  refine (congrArg (Gm.pointsEquiv S Z)
    (comp_groupHom_sum (G := splitTorus.commGroupScheme S (ULift.{u} (OffPivot p)))
      s Finset.univ fun c => weightCoord p i c.down •
        splitTorus.proj S (ULift.{u} (OffPivot p)) c)).trans ?_
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro c _
  refine (congrArg (Gm.pointsEquiv S Z)
    (comp_groupHom_zsmul (G := splitTorus.commGroupScheme S (ULift.{u} (OffPivot p)))
      s (weightCoord p i c.down)
      (splitTorus.proj S (ULift.{u} (OffPivot p)) c))).trans ?_
  rw [map_zpow, splitTorus.comp_proj]

/-- The standard diagonal torus has exactly the entries supplied by its weight characters. -/
theorem coe_pointsEquiv_diagonalTorus_weights (p : n) (R : CommRingCat.{u})
    {Z : Over (Spec R)}
    (s : Z ⟶ (splitTorus (Spec R) (ULift.{u} (OffPivot p))).X) :
    (pointsEquiv n R Z (s ≫ (diagonalTorus p R).hom.hom) : Matrix n n Γ(Z.left, ⊤)) =
      Matrix.diagonal fun i =>
        ((Gm.pointsEquiv _ Z
          (s ≫ (CommGroupScheme.groupHom (diagonalWeight p (Spec R) i)).hom.hom) :
            Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) := by
  simp only [pointsEquiv_diagonalTorus, coe_torusUnits, pointsEquiv_diagonalWeight]

end SpecialLinear

namespace LocalGroupIso

variable {S : Scheme.{u}} {U : Over S} {G H : GroupScheme S}

/-- The actual inverse over the cover has the inverse local value on each relative test. -/
theorem coverPointsEquiv_toBaseChangeIso_inv (e : LocalGroupIso G H U)
    {Z : Over S} (a : Z ⟶ U)
    (y : coverTest a ⟶ ((baseChange U.hom).obj H).X) :
    coverPointsEquiv G a (y ≫ e.toBaseChangeIso.inv.hom.hom) =
      (e.toFun a).symm (coverPointsEquiv H a y) := by
  have ha : (coverTestIso a).inv ≫ baseChangeTestPoint (coverTest a) = a := by
    apply Over.OverMorphism.ext
    exact Category.id_comp a.left
  have hn :
      (e.toFun ((coverTestIso a).inv ≫ baseChangeTestPoint (coverTest a))).symm
          ((coverTestIso a).inv ≫ baseChangePointsEquiv U.hom H (coverTest a) y) =
        (coverTestIso a).inv ≫ (e.toFun (baseChangeTestPoint (coverTest a))).symm
          (baseChangePointsEquiv U.hom H (coverTest a) y) :=
    e.symm.naturality (coverTestIso a).inv
      (baseChangeTestPoint (coverTest a))
      (baseChangePointsEquiv U.hom H (coverTest a) y)
  rw [ha] at hn
  change (coverTestIso a).inv ≫
    baseChangePointsEquiv U.hom G (coverTest a)
      (y ≫ e.toBaseChangeIso.inv.hom.hom) = _
  rw [e.toBaseChangeIso_inv_points]
  exact hn.symm

end LocalGroupIso

namespace Gm

/-- The multiplicative-group comparison preserves the unit at a specified cover point. -/
theorem pointsEquiv_coverPointsEquiv {S : Scheme.{u}} {U : Over S}
    {Z : Over S} (a : Z ⟶ U)
    (x : LocalGroupIso.coverTest a ⟶ ((baseChange U.hom).obj (Gm S).toGrp).X) :
    pointsEquiv S Z (LocalGroupIso.coverPointsEquiv (Gm S).toGrp a x) =
      pointsEquiv U.left (LocalGroupIso.coverTest a)
        (x ≫ (baseChangeIso U.hom).hom.hom.hom) := by
  rw [pointsEquiv_baseChangeIso_hom, baseChangeUnitsEquiv_apply]
  change pointsEquiv S Z ((LocalGroupIso.coverTestIso a).inv ≫
      baseChangePointsEquiv U.hom (Gm S).toGrp (LocalGroupIso.coverTest a) x) = _
  rw [pointsEquiv_naturality]
  apply Units.ext
  change (Scheme.Hom.appTop (𝟙 Z.left)) _ = _
  simp

end Gm

end Langlands.GroupScheme
