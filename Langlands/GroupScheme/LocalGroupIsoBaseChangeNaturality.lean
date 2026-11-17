import Langlands.GroupScheme.LocalGroupIsoBaseChangeEquivalence
import Langlands.GroupScheme.LocalGroupIsoRefinement
import Langlands.GroupScheme.Descent.DatumRelation
import Langlands.GroupScheme.AutomorphicAction.BaseChange
import Langlands.GroupScheme.AutomorphicActionPointIso

/-! # Pullback and action compatibility for actual local isomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.LocalGroupIso

variable {S : Scheme.{u}} {G H A : GroupScheme S} {U V : Over S}

/-- The lift of an original group point is the canonical pullback lift. -/
theorem coverPointsEquiv_symm_left (G : GroupScheme S) {T : Over S}
    (b : T ⟶ U) (g : T ⟶ G.X) :
    ((coverPointsEquiv G b).symm g).left =
      pullback.lift g.left b.left ((Over.w g).trans (Over.w b).symm) := by
  apply pullback.hom_ext
  · have h := congrArg (fun f => f.left) ((coverPointsEquiv G b).apply_symm_apply g)
    simpa only [coverPointsEquiv_left, pullback.lift_fst] using h
  · rw [pullback.lift_snd]
    exact Over.w ((coverPointsEquiv G b).symm g)

/-- Refinement of a local family is the actual pullback isomorphism, with
the equal base maps explicitly identified. -/
theorem ofBaseChangeIso_refine
    (e : (baseChange U.hom).obj G ≅ (baseChange U.hom).obj H)
    (r : V ⟶ U) :
    (ofBaseChangeIso e).refine r =
      ofBaseChangeIso (Descent.pullIso r.left (Over.w r) (Over.w r) e) := by
  apply ext_toFun
  intro T b g
  apply Over.OverMorphism.ext
  change ((ofBaseChangeIso e).toFun (b ≫ r) g).left = _
  rw [ofBaseChangeIso_toFun_left, ofBaseChangeIso_toFun_left,
    coverPointsEquiv_symm_left, coverPointsEquiv_symm_left]
  symm
  exact Descent.pullHom_eval r.left (Over.w r) (Over.w r) e.hom
    g.left b.left ((Over.w g).trans (Over.w b).symm)

/-- Recovery of actual isomorphisms commutes with arbitrary refinement. -/
theorem toBaseChangeIso_refine (e : LocalGroupIso G H U) (r : V ⟶ U) :
    (e.refine r).toBaseChangeIso =
      Descent.pullIso r.left (Over.w r) (Over.w r) e.toBaseChangeIso := by
  have h := congrArg (fun f : LocalGroupIso G H V => f.toBaseChangeIso)
    (ofBaseChangeIso_refine e.toBaseChangeIso r)
  simpa only [ofBaseChangeIso_toBaseChangeIso, toBaseChangeIso_ofBaseChangeIso] using h

/-- A pulled-back section projects to its original point after every refinement. -/
theorem baseChangePointsEquiv_constantSection
    (x : Over.mk (𝟙 U.left) ⟶ ((baseChange U.hom).obj A).X)
    (T : Over U.left) :
    baseChangePointsEquiv U.hom A T
        (((baseChange U.hom).obj A).constantPoint x T) =
      baseChangeTestPoint T ≫ baseChangeBasePointsEquiv U.hom A x := by
  apply Over.OverMorphism.ext
  simp only [baseChangePointsEquiv_left, constantPoint, Over.comp_left,
    Over.homMk_left, baseChangeTestPoint, baseChangeBasePointsEquiv_left,
    Category.assoc]

/-- Twisting by an acting point is actual precomposition by the corresponding
automorphism of the pulled-back group. -/
theorem toBaseChangeIso_twist (e : LocalGroupIso G H U)
    (a : AutomorphicAction A G) (d : U ⟶ A.X) :
    (e.twist a d).toBaseChangeIso =
      (a.baseChange U.hom).basePointIso
        ((baseChangeBasePointsEquiv U.hom A).symm d) ≪≫ e.toBaseChangeIso := by
  symm
  apply (e.twist a d).toBaseChangeIso_unique
  intro T g
  change baseChangePointsEquiv U.hom H T
      ((g ≫ ((a.baseChange U.hom).basePointIso
        ((baseChangeBasePointsEquiv U.hom A).symm d)).hom.hom.hom) ≫
          e.toBaseChangeIso.hom.hom.hom) =
    e.toFun (baseChangeTestPoint T)
      (a.act (baseChangeTestPoint T ≫ d) (baseChangePointsEquiv U.hom G T g))
  rw [e.toBaseChangeIso_hom_points, AutomorphicAction.comp_basePointIso_hom,
    a.baseChangePointsEquiv_act, baseChangePointsEquiv_constantSection,
    MulEquiv.apply_symm_apply]

end Langlands.GroupScheme.LocalGroupIso
