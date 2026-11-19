import Langlands.GroupScheme.RelativeUnipotent.DisjointBundlePoints

/-! # Exact recovery of original module point charts on a coproduct component -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent.DisjointBundlePoints.ComponentCharts

variable {I : Type u} {Z : I → Scheme.{u}} {V : GroupScheme (∐ Z)}
  {M : (∐ Z).Modules} (C : ComponentCharts Z V M)

set_option maxRecDepth 2000 in
/-- The assembled original point chart recovers the prescribed original
component chart on every test over that component, through the actual
canonical module composition comparison. -/
lemma pointSectionEquiv_baseChange (i : I) (W : Over (Z i))
    (x : W ⟶ ((baseChange (Sigma.ι Z i)).obj V).X) :
    (C.pointSectionEquiv ((Over.map (Sigma.ι Z i)).obj W)
      (baseChangePointsEquiv (Sigma.ι Z i) V W x)).toAdd =
        baseChangeSectionEquiv (Sigma.ι Z i) M W (C.equiv i W x).toAdd := by
  let B := (Over.map (Sigma.ι Z i)).obj W
  let y := baseChangePointsEquiv (Sigma.ι Z i) V W x
  let A := componentTest Z B i
  let q : W ⟶ A := (Over.mapPullbackAdj (Sigma.ι Z i)).unit.app W
  let j := (Over.map (Sigma.ι Z i)).map q
  let z := restrictedPoint Z V B i y
  have hq : j ≫ componentMap Z B i = 𝟙 B :=
    (Over.mapPullbackAdj (Sigma.ι Z i)).left_triangle_components W
  have hz : q ≫ z = x := by
    apply (baseChangePointsEquiv (Sigma.ι Z i) V W).injective
    rw [baseChangePointsEquiv_naturality, point_restriction, ← Category.assoc, hq,
      Category.id_comp]
  have hid : sectionPullback M (𝟙 B) (C.pointSectionEquiv B y).toAdd =
      (C.pointSectionEquiv B y).toAdd := by
    simpa only [Category.id_comp] using
      (C.pointSectionEquiv_natural B B (𝟙 B) y).symm
  have H := congrArg (sectionPullback M j) (C.pointSectionEquiv_component B y i)
  change sectionPullback M j
      (sectionPullback M (componentMap Z B i) (C.pointSectionEquiv B y).toAdd) =
    sectionPullback M j (baseChangeSectionEquiv (Sigma.ι Z i) M A
      (C.equiv i A z).toAdd) at H
  rw [sectionPullback_comp, hq, hid] at H
  have hn := baseChangeSectionEquiv_naturality (Sigma.ι Z i) M q (C.equiv i A z).toAdd
  change baseChangeSectionEquiv (Sigma.ι Z i) M W
      (sectionPullback ((Scheme.Modules.pullback (Sigma.ι Z i)).obj M) q
        (C.equiv i A z).toAdd) =
    sectionPullback M j (baseChangeSectionEquiv (Sigma.ι Z i) M A
      (C.equiv i A z).toAdd) at hn
  rw [← hn, ← C.natural i A W q z, hz] at H
  exact H

end Langlands.GroupScheme.RelativeUnipotent.DisjointBundlePoints.ComponentCharts
