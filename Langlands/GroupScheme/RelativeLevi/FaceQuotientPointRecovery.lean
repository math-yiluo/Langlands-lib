import Langlands.GroupScheme.RelativeLevi.FaceQuotientComponentRecovery
import Langlands.GroupScheme.RelativeUnipotent.DisjointPointChartRecovery

/-! # Exact original quotient point coordinates on a cover component -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent.LiftedModuleCharts

/-- The actual lifted point retains its original underlying morphism. -/
lemma liftPointsEquiv_original {S X : Scheme.{u}} (p : X ⟶ S) (V : GroupScheme S)
    (T : Over S) (a : T.left ⟶ X) (ha : a ≫ p = T.hom) (x : T ⟶ V.X) :
    (liftPointsEquiv p V T a ha x).left ≫ pullback.fst V.X.hom p = x.left := by
  change (baseChangePointsEquiv p V (Over.mk a) (liftPointsEquiv p V T a ha x)).left = _
  simp [liftPointsEquiv, sourcePointsEquiv, liftedTestIso]

/-- Direct and iterated lifting of the same original point agree through the
prescribed actual group pullback comparison. -/
lemma liftPointsEquiv_tower {S X Y : Scheme.{u}} (p : X ⟶ S) (j : Y ⟶ X)
    (q : Y ⟶ S) (hj : j ≫ p = q) (V : GroupScheme S)
    (T : Over S) (b : T.left ⟶ Y) (hb : b ≫ q = T.hom) (x : T ⟶ V.X) :
    baseChangePointsEquiv j ((baseChange p).obj V) (Over.mk b)
        (liftPointsEquiv q V T b hb x ≫
          (Descent.pullbackComparison p j q hj V).inv.hom.hom) =
      liftPointsEquiv p V T (b ≫ j) (by rw [Category.assoc, hj, hb]) x := by
  apply (baseChangePointsEquiv p V (Over.mk (b ≫ j))).injective
  apply Over.OverMorphism.ext
  change (liftPointsEquiv q V T b hb x).left ≫
      (Descent.pullbackComparison p j q hj V).inv.hom.hom.left ≫
      pullback.fst ((baseChange p).obj V).X.hom j ≫ pullback.fst V.X.hom p =
    (liftPointsEquiv p V T (b ≫ j) _ x).left ≫ pullback.fst V.X.hom p
  rw [Descent.pullbackComparison_inv_fst, liftPointsEquiv_original, liftPointsEquiv_original]

end Langlands.GroupScheme.RelativeUnipotent.LiftedModuleCharts

namespace Langlands.GroupScheme.RelativeLevi.FiniteParabolicFaceCover

open RelativeUnipotent

variable {S : Scheme.{u}} [IsAffine S] {G H U : GroupScheme S}
  [IsAffineHom G.X.hom] {p : H ⟶ G}
  (D : FiniteParabolicFaceCover p)
  (r : U ⟶ H) (hG : IsReductive G) (hp : IsRelativeParabolicSubgroup p)
  (hr : IsRelativeUnipotentRadical r)

omit [IsAffine S] in
set_option maxRecDepth 2000 in
/-- The assembled original layer point chart restricts to the prescribed
original component module chart on every test. -/
lemma layerBundlePoints_component (d : ℕ) (i : D.Index)
    (T : Over (Spec (D.charts i.down).2.ring))
    (x : T ⟶ ((baseChange (D.componentMap i)).obj (D.layerGroup d)).X) :
    (D.layerBundlePoints d ((Over.map (D.componentMap i)).obj T)
      (baseChangePointsEquiv (D.componentMap i) (D.layerGroup d) T x)).toAdd =
        baseChangeSectionEquiv (D.componentMap i) (D.layerBundle d) T
          ((D.layerComponentCharts d).equiv i T x).toAdd :=
  (D.layerComponentCharts d).pointSectionEquiv_baseChange i T x

/-- Original global quotient points in one original vector quotient chart. -/
def quotientComponentPoint (d : ℕ) (i : D.Index) (T : Over S)
    (b : T.left ⟶ Spec (D.charts i.down).2.ring)
    (hb : b ≫ (D.charts i.down).2.projection = T.hom)
    (x : T ⟶ (D.globalFaceQuotientData r hG hp hr d).group.X) :
    Over.mk b ⟶ ((D.charts i.down).2.layerGroup d).X :=
  LiftedModuleCharts.liftPointsEquiv (D.charts i.down).2.projection
      (D.globalFaceQuotientData r hG hp hr d).group T b hb x ≫
    (D.globalFaceQuotientComponentIso r hG hp hr d i).hom.hom.hom

set_option maxRecDepth 2000 in
/-- The original lifted module chart recovers the original vector coordinates,
through only the prescribed canonical module and actual component maps. -/
lemma globalFaceQuotientCharts_component (d : ℕ) (i : D.Index) (T : Over S)
    (b : T.left ⟶ Spec (D.charts i.down).2.ring)
    (hb : b ≫ (D.charts i.down).2.projection = T.hom)
    (x : T ⟶ (D.globalFaceQuotientData r hG hp hr d).group.X) :
    ((Scheme.Modules.pullback b).map (D.layerBundlePieceIso d i).hom).app ⊤
      ((baseChangeSectionEquiv (D.componentMap i) (D.layerBundle d) (Over.mk b)).symm
        ((D.globalFaceQuotientCharts r hG hp hr d).equiv T (b ≫ D.componentMap i)
          (by rw [Category.assoc, D.componentMap_comp_groupsBaseMap, hb]) x).toAdd) =
      (freeVectorBundlePoints (CommRingCat.of (D.charts i.down).2.ring)
        (D.layerRank d i) (Over.mk b) (D.quotientComponentPoint r hG hp hr d i T b hb x)).toAdd := by
  let Q := (D.globalFaceQuotientData r hG hp hr d).group
  let A := Over.mk b
  let z := LiftedModuleCharts.liftPointsEquiv (D.charts i.down).2.projection Q T b hb x ≫
    (Descent.pullbackComparison D.groupsBaseMap (D.componentMap i)
      (D.charts i.down).2.projection (D.componentMap_comp_groupsBaseMap i) Q).inv.hom.hom
  let w := z ≫ ((baseChange (D.componentMap i)).map
    (D.globalFaceQuotientData r hG hp hr d).coverIso.hom).hom.hom
  have hz := LiftedModuleCharts.liftPointsEquiv_tower D.groupsBaseMap (D.componentMap i)
    (D.charts i.down).2.projection (D.componentMap_comp_groupsBaseMap i) Q T b hb x
  have hw : baseChangePointsEquiv (D.componentMap i) (D.layerGroup d) A w =
      LiftedModuleCharts.liftPointsEquiv D.groupsBaseMap Q T (b ≫ D.componentMap i)
        (by rw [Category.assoc, D.componentMap_comp_groupsBaseMap, hb]) x ≫
          (D.globalFaceQuotientData r hG hp hr d).coverIso.hom.hom.hom := by
    change baseChangePointsEquiv (D.componentMap i) (D.layerGroup d) A
      (z ≫ ((baseChange (D.componentMap i)).map
        (D.globalFaceQuotientData r hG hp hr d).coverIso.hom).hom.hom) = _
    rw [baseChangePointsEquiv_comp]
    exact congrArg (fun v => v ≫
      (D.globalFaceQuotientData r hG hp hr d).coverIso.hom.hom.hom) hz
  have hg : ((D.globalFaceQuotientCharts r hG hp hr d).equiv T (b ≫ D.componentMap i)
        (by rw [Category.assoc, D.componentMap_comp_groupsBaseMap, hb]) x).toAdd =
      (D.layerBundlePoints d ((Over.map (D.componentMap i)).obj A)
        (baseChangePointsEquiv (D.componentMap i) (D.layerGroup d) A w)).toAdd := by
    change (D.layerBundlePoints d (Over.mk (b ≫ D.componentMap i))
      (LiftedModuleCharts.liftPointsEquiv D.groupsBaseMap Q T (b ≫ D.componentMap i) _
        x ≫ (D.globalFaceQuotientData r hG hp hr d).coverIso.hom.hom.hom)).toAdd = _
    rw [hw]
    rfl
  rw [hg, D.layerBundlePoints_component, AddEquiv.symm_apply_apply]
  have Hmap := moduleIsoPoints_map (D.layerBundlePieceIso d i)
    (D.layerComponentFreePoints d i) A w
  exact Hmap

end Langlands.GroupScheme.RelativeLevi.FiniteParabolicFaceCover
