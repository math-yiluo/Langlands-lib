import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleTorus
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # Descent of diagonal special-linear weights to a split torus -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SpecialLinear

/-- The special-linear model comparison preserves the matrix at a cover point. -/
theorem pointsEquiv_coverPointsEquiv (n : Type) [Fintype n] [DecidableEq n]
    {R R' : CommRingCat.{u}} (b : Spec R' ⟶ Spec R)
    {Z : Over (Spec R)} (a : Z ⟶ Over.mk b)
    (x : LocalGroupIso.coverTest a ⟶ ((baseChange b).obj (groupScheme n R)).X) :
    pointsEquiv n R Z (LocalGroupIso.coverPointsEquiv (groupScheme n R) a x) =
      pointsEquiv n R' (LocalGroupIso.coverTest a)
        (x ≫ (baseChangeModelIso n b).hom.hom.hom) := by
  rw [pointsEquiv_baseChangeModelIso_hom]
  change pointsEquiv n R Z ((LocalGroupIso.coverTestIso a).inv ≫
      baseChangePointsEquiv b (groupScheme n R) (LocalGroupIso.coverTest a) x) = _
  rw [pointsEquiv_naturality]
  ext i j
  rfl

end SpecialLinear

namespace characterLattice

/-- Evaluating a base-changed character at a cover point preserves its unit. -/
theorem pointsEquiv_baseChange_cover {S : Scheme.{u}} {U : Over S}
    (T : CommGroupScheme S) (χ : characterLattice T)
    {Z : Over S} (a : Z ⟶ U)
    (s : LocalGroupIso.coverTest a ⟶ ((GroupScheme.baseChange U.hom).obj T.toGrp).X) :
    Gm.pointsEquiv S Z
        (LocalGroupIso.coverPointsEquiv T.toGrp a s ≫
          (CommGroupScheme.groupHom χ).hom.hom) =
      Gm.pointsEquiv U.left (LocalGroupIso.coverTest a)
        (s ≫ (CommGroupScheme.groupHom (baseChange U.hom T χ)).hom.hom) := by
  rw [← LocalGroupIso.coverPointsEquiv_comp, Gm.pointsEquiv_coverPointsEquiv]
  rfl

end characterLattice

namespace SpecialLinearTitsCocycle

variable {K L : Type u} [Field K] [Field L]
variable (b : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (hT : IsSplitTorus T.toGrp)
    {n : Type} [Fintype n] [DecidableEq n] (p : n)
    (q : (CommGroupScheme.baseChange b).obj T ⟶
      splitTorus.commGroupScheme (Spec (CommRingCat.of L))
        (ULift.{u} (SpecialLinear.OffPivot p)))

/-- A diagonal weight over the extension, descended through the canonical character equivalence. -/
def descendedDiagonalWeight (i : n) : characterLattice T :=
  (characterLattice.baseChangeEquiv b T hT).symm
    (q ≫ SpecialLinear.diagonalWeight p (Spec (CommRingCat.of L)) i)

/-- Scalar extension of the descended weight is the original diagonal character. -/
@[simp] theorem baseChange_descendedDiagonalWeight (i : n) :
    characterLattice.baseChange b T (descendedDiagonalWeight b T hT p q i) =
      q ≫ SpecialLinear.diagonalWeight p (Spec (CommRingCat.of L)) i :=
  (characterLattice.baseChangeEquiv b T hT).apply_symm_apply _

/-- Character differences descend together with the individual diagonal weights. -/
theorem eq_descendedDiagonalWeight_sub (α : characterLattice T) (i j : n)
    (hα : characterLattice.baseChange b T α =
      q ≫ (SpecialLinear.diagonalWeight p (Spec (CommRingCat.of L)) i -
        SpecialLinear.diagonalWeight p (Spec (CommRingCat.of L)) j)) :
    α = descendedDiagonalWeight b T hT p q i - descendedDiagonalWeight b T hT p q j := by
  apply (characterLattice.baseChangeEquiv b T hT).injective
  simpa only [map_sub, characterLattice.baseChangeEquiv_apply,
    baseChange_descendedDiagonalWeight, Preadditive.comp_sub] using hα

/-- A diagonal factorization over the cover gives the diagonal formula on every original test. -/
theorem diagonal_of_baseChangeFactorization
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (E : LocalGroupIso (SpecialLinear.groupScheme n (CommRingCat.of K)) G (Over.mk b))
    (f : T.toGrp ⟶ G)
    (hfactor : (GroupScheme.baseChange b).map f ≫ E.toBaseChangeIso.inv ≫
        (SpecialLinear.baseChangeModelIso n b).hom =
      CommGroupScheme.groupHom q ≫ SpecialLinear.diagonalTorus p (CommRingCat.of L))
    (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ Over.mk b) (s : Z ⟶ T.X) :
    (SpecialLinear.pointsEquiv n (CommRingCat.of K) Z
        ((E.toFun a).symm (s ≫ f.hom.hom)) : Matrix n n Γ(Z.left, ⊤)) =
      Matrix.diagonal fun i =>
        ((Gm.pointsEquiv _ Z
          (s ≫ (CommGroupScheme.groupHom
            (descendedDiagonalWeight b T hT p q i)).hom.hom) : Γ(Z.left, ⊤)ˣ) :
          Γ(Z.left, ⊤)) := by
  let sL := (LocalGroupIso.coverPointsEquiv T.toGrp a).symm s
  have hs : LocalGroupIso.coverPointsEquiv T.toGrp a sL = s :=
    (LocalGroupIso.coverPointsEquiv T.toGrp a).apply_symm_apply s
  have hp : LocalGroupIso.coverPointsEquiv G a
      (sL ≫ ((GroupScheme.baseChange b).map f).hom.hom) = s ≫ f.hom.hom :=
    (LocalGroupIso.coverPointsEquiv_comp (U := Over.mk b) f a sL).trans
      (congrArg (fun t => t ≫ f.hom.hom) hs)
  have he := LocalGroupIso.coverPointsEquiv_toBaseChangeIso_inv E a
    (sL ≫ ((GroupScheme.baseChange b).map f).hom.hom)
  rw [hp] at he
  have hm := SpecialLinear.pointsEquiv_coverPointsEquiv n b a
    ((sL ≫ ((GroupScheme.baseChange b).map f).hom.hom) ≫ E.toBaseChangeIso.inv.hom.hom)
  rw [he] at hm
  have hf : ((sL ≫ ((GroupScheme.baseChange b).map f).hom.hom) ≫
        E.toBaseChangeIso.inv.hom.hom) ≫
        (SpecialLinear.baseChangeModelIso n b).hom.hom.hom =
      (sL ≫ (CommGroupScheme.groupHom q).hom.hom) ≫
        (SpecialLinear.diagonalTorus p (CommRingCat.of L)).hom.hom := by
    exact congrArg (fun v => sL ≫ v.hom.hom) hfactor
  rw [hf] at hm
  rw [hm, SpecialLinear.coe_pointsEquiv_diagonalTorus_weights]
  congr 1
  funext i
  have hc := characterLattice.pointsEquiv_baseChange_cover T
    (descendedDiagonalWeight b T hT p q i) a sL
  rw [hs] at hc
  have hχ : sL ≫ (CommGroupScheme.groupHom
        (characterLattice.baseChange b T (descendedDiagonalWeight b T hT p q i))).hom.hom =
      (sL ≫ (CommGroupScheme.groupHom q).hom.hom) ≫
        (CommGroupScheme.groupHom
          (SpecialLinear.diagonalWeight p (Spec (CommRingCat.of L)) i)).hom.hom :=
    (congrArg (fun v : characterLattice ((CommGroupScheme.baseChange b).obj T) =>
      sL ≫ (CommGroupScheme.groupHom v).hom.hom)
      (baseChange_descendedDiagonalWeight b T hT p q i)).trans
        (comp_groupHom_comp (G := (CommGroupScheme.baseChange b).obj T) sL q
          (SpecialLinear.diagonalWeight p (Spec (CommRingCat.of L)) i))
  exact congrArg (fun v : Γ(Z.left, ⊤)ˣ => (v : Γ(Z.left, ⊤)))
    (hc.trans (congrArg (Gm.pointsEquiv (Spec (CommRingCat.of L))
      (LocalGroupIso.coverTest a)) hχ)).symm

end SpecialLinearTitsCocycle

end Langlands.GroupScheme
