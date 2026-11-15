import Langlands.GroupScheme.LocalGroupIsoBaseChangeEquivalence
import Langlands.GroupScheme.LocalGroupIsoRefinement
import Langlands.GroupScheme.AutomorphicAction.BaseChange
import Langlands.GroupScheme.AutomorphicActionPointIso
import Langlands.GroupScheme.Rational.InnerDiscrepancy

/-! # Actual relative automorphisms representing inner discrepancies -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace LocalGroupIso

variable {S : Scheme.{u}} {G H A : GroupScheme S} {U : Over S}
  (e : LocalGroupIso G H U)

/-- The natural automorphisms comparing two specified cover points. -/
def discrepancyFamily {T : Over S} (b c : T ⟶ U) : LocalGroupIso G G T where
  toFun t := (e.toFun (t ≫ c)).trans (e.toFun (t ≫ b)).symm
  naturality t d g := by
    change (e.toFun ((t ≫ d) ≫ b)).symm (e.toFun ((t ≫ d) ≫ c) (t ≫ g)) =
      t ≫ (e.toFun (d ≫ b)).symm (e.toFun (d ≫ c) g)
    rw [Category.assoc, Category.assoc, e.naturality]
    exact e.symm.naturality t (d ≫ b) (e.toFun (d ≫ c) g)

/-- The actual automorphism over the test scheme comparing the two local maps. -/
def discrepancyIso {T : Over S} (b c : T ⟶ U) :
    (GroupScheme.baseChange T.hom).obj G ≅ (GroupScheme.baseChange T.hom).obj G :=
  (e.discrepancyFamily b c).toBaseChangeIso

/-- The actual discrepancy automorphism has the expected effect on every test. -/
theorem discrepancyIso_toFun {T W : Over S} (b c : T ⟶ U) (t : W ⟶ T)
    (g : W ⟶ G.X) :
    (ofBaseChangeIso (e.discrepancyIso b c)).toFun t g =
      (e.toFun (t ≫ b)).symm (e.toFun (t ≫ c) g) := by
  simp only [discrepancyIso, ofBaseChangeIso_toBaseChangeIso]
  rfl

end LocalGroupIso

namespace AutomorphicAction

variable {S : Scheme.{u}} {G A : GroupScheme S} (a : AutomorphicAction A G)

/-- Evaluate the base-changed action at the section determined by a relative point. -/
def relativePointIso {T : Over S} (x : T ⟶ A.X) :
    (GroupScheme.baseChange T.hom).obj G ≅ (GroupScheme.baseChange T.hom).obj G :=
  (a.baseChange T.hom).basePointIso
    ((LocalGroupIso.coverPointsEquiv A (𝟙 T)).symm x)

/-- Projection identifies the pulled-back constant section with the original point. -/
theorem relativePoint_constantPoint {T : Over S} (x : T ⟶ A.X)
    (W : Over T.left) :
    baseChangePointsEquiv T.hom A W
        (((GroupScheme.baseChange T.hom).obj A).constantPoint
          ((LocalGroupIso.coverPointsEquiv A (𝟙 T)).symm x) W) =
      LocalGroupIso.baseChangeTestPoint W ≫ x := by
  apply Over.OverMorphism.ext
  rw [baseChangePointsEquiv_left]
  change W.hom ≫ ((LocalGroupIso.coverPointsEquiv A (𝟙 T)).symm x).left ≫
    CategoryTheory.Limits.pullback.fst A.X.hom T.hom = W.hom ≫ x.left
  have hx := congrArg (fun f => f.left)
    ((LocalGroupIso.coverPointsEquiv A (𝟙 T)).apply_symm_apply x)
  rw [LocalGroupIso.coverPointsEquiv_left] at hx
  rw [hx]

/-- The actual evaluated automorphism acts as the original action after projection. -/
theorem relativePointIso_points {T : Over S} (x : T ⟶ A.X)
    (W : Over T.left) (g : W ⟶ ((GroupScheme.baseChange T.hom).obj G).X) :
    baseChangePointsEquiv T.hom G W (g ≫ (a.relativePointIso x).hom.hom.hom) =
      a.act (LocalGroupIso.baseChangeTestPoint W ≫ x)
        (baseChangePointsEquiv T.hom G W g) := by
  rw [relativePointIso, comp_basePointIso_hom, baseChangePointsEquiv_act,
    relativePoint_constantPoint]

/-- Passing the evaluated action back to a local family recovers its all-test action. -/
theorem relativePointIso_toFun {T W : Over S} (x : T ⟶ A.X)
    (t : W ⟶ T) (g : W ⟶ G.X) :
    (LocalGroupIso.ofBaseChangeIso (a.relativePointIso x)).toFun t g =
      a.act (t ≫ x) g := by
  change LocalGroupIso.coverPointsEquiv G t
    (((LocalGroupIso.coverPointsEquiv G t).symm g) ≫
      (a.relativePointIso x).hom.hom.hom) = _
  change (LocalGroupIso.coverTestIso t).inv ≫
    baseChangePointsEquiv T.hom G (LocalGroupIso.coverTest t) _ = _
  rw [relativePointIso_points, a.naturality]
  have ht : (LocalGroupIso.coverTestIso t).inv ≫
      LocalGroupIso.baseChangeTestPoint (LocalGroupIso.coverTest t) = t := by
    apply Over.OverMorphism.ext
    change 𝟙 W.left ≫ t.left = t.left
    exact Category.id_comp _
  have hg : (LocalGroupIso.coverTestIso t).inv ≫
      baseChangePointsEquiv T.hom G (LocalGroupIso.coverTest t)
        ((LocalGroupIso.coverPointsEquiv G t).symm g) = g :=
    (LocalGroupIso.coverPointsEquiv G t).apply_symm_apply g
  rw [← Category.assoc, ht, hg]

end AutomorphicAction

namespace LocalGroupIso

variable {S : Scheme.{u}} {G H A : GroupScheme S} {U : Over S}
  (e : LocalGroupIso G H U) (a : AutomorphicAction A G)

/-- The all-refinement discrepancy equation is equality of actual automorphisms
on the pullback to the test scheme. -/
theorem representsDiscrepancy_iff_discrepancyIso {T : Over S}
    (b c : T ⟶ U) (x : T ⟶ A.X) :
    e.RepresentsDiscrepancy a b c x ↔
      e.discrepancyIso b c = a.relativePointIso x := by
  constructor
  · intro hx
    apply (baseChangeIsoEquiv (G := G) (H := G) (U := T)).injective
    apply ext_toFun
    intro W t g
    change (ofBaseChangeIso (e.discrepancyIso b c)).toFun t g =
      (ofBaseChangeIso (a.relativePointIso x)).toFun t g
    rw [discrepancyIso_toFun, AutomorphicAction.relativePointIso_toFun]
    apply (e.toFun (t ≫ b)).injective
    rw [MulEquiv.apply_symm_apply]
    exact (hx t g).symm
  · intro h W t g
    have ht := congrArg (fun E => (ofBaseChangeIso E).toFun t g) h
    rw [discrepancyIso_toFun, AutomorphicAction.relativePointIso_toFun] at ht
    rw [← ht]
    exact MulEquiv.apply_symm_apply _ _

/-- The discrepancy is the composite of the two actual local identifications. -/
theorem discrepancyIso_eq_composite {T : Over S} (b c : T ⟶ U) :
    e.discrepancyIso b c =
      (e.refine c).toBaseChangeIso ≪≫ (e.refine b).toBaseChangeIso.symm := by
  apply Iso.ext
  apply hom_ext_points
  intro W g
  apply (baseChangePointsEquiv T.hom G W).injective
  rw [discrepancyIso, toBaseChangeIso_hom_points]
  change (e.toFun (baseChangeTestPoint W ≫ b)).symm
      (e.toFun (baseChangeTestPoint W ≫ c) (baseChangePointsEquiv T.hom G W g)) = _
  rw [Iso.trans_hom, Iso.symm_hom, Grp.comp_hom_hom, ← Category.assoc,
    toBaseChangeIso_inv_points, toBaseChangeIso_hom_points]
  rfl

/-- Inner discrepancy is exactly pointwise innerness of the actual relative automorphisms. -/
theorem hasInnerDiscrepancy_iff_discrepancyIso :
    e.HasInnerDiscrepancy a ↔
      ∀ {T : Over S} (b c : T ⟶ U),
        ∃ x : T ⟶ A.X, e.discrepancyIso b c = a.relativePointIso x := by
  constructor
  · intro he T b c
    obtain ⟨x, hx⟩ := he b c
    exact ⟨x, (e.representsDiscrepancy_iff_discrepancyIso a b c x).mp hx⟩
  · intro he T b c
    obtain ⟨x, hx⟩ := he b c
    exact ⟨x, (e.representsDiscrepancy_iff_discrepancyIso a b c x).mpr hx⟩

end LocalGroupIso

end Langlands.GroupScheme
