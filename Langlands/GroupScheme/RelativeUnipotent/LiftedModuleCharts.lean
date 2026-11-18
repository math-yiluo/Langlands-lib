import Langlands.GroupScheme.RelativeUnipotent.LinearModuleChartDescent
import Langlands.GroupScheme.RelativeUnipotent.VectorBundleBaseChangeCocycle

/-! # Actual module point charts on tests lifted to a cover -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.Scheme.Modules.LineBundleFlatDescent
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent

variable {S X : Scheme.{u}} (p : X ⟶ S) (V : GroupScheme S) (F : X.Modules)

/-- Actual natural point/section charts on every test with a chosen lift to the cover.
No compatibility between different lifts is built into this data. -/
structure LiftedModuleCharts where
  equiv : ∀ (T : Over S) (a : T.left ⟶ X) (_ha : a ≫ p = T.hom),
    (T ⟶ V.X) ≃* Multiplicative
      (GlobalSections ((Scheme.Modules.pullback a).obj F))
  natural : ∀ (T W : Over S) (b : W ⟶ T) (a : T.left ⟶ X)
    (ha : a ≫ p = T.hom) (x : T ⟶ V.X),
    (equiv W (b.left ≫ a) (by rw [Category.assoc, ha, Over.w b]) (b ≫ x)).toAdd =
      ((Scheme.Modules.pullbackComp b.left a).hom.app F).app ⊤
        (pullbackSection b.left ((Scheme.Modules.pullback a).obj F)
          (equiv T a ha x).toAdd)

namespace LiftedModuleCharts

variable {p V F}

/-- The original test and the lifted test have the same underlying scheme. -/
def liftedTestIso (T : Over S) (a : T.left ⟶ X) (ha : a ≫ p = T.hom) :
    (Over.map p).obj (Over.mk a) ≅ T :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 T.left ≫ T.hom = a ≫ p
    rw [Category.id_comp]
    exact ha.symm)

/-- Multiplicative point transport under an actual isomorphism of source tests. -/
def sourcePointsEquiv {T W : Over S} (e : T ≅ W) (V : GroupScheme S) :
    (T ⟶ V.X) ≃* (W ⟶ V.X) where
  toFun x := e.inv ≫ x
  invFun x := e.hom ≫ x
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := MonObj.comp_mul _ _ _

/-- Lift a point to the actual pullback group, retaining its original underlying point. -/
def liftPointsEquiv (p : X ⟶ S) (V : GroupScheme S) (T : Over S)
    (a : T.left ⟶ X) (ha : a ≫ p = T.hom) :
    (T ⟶ V.X) ≃* (Over.mk a ⟶ ((baseChange p).obj V).X) :=
  (sourcePointsEquiv (liftedTestIso T a ha).symm V).trans
    (baseChangePointsEquiv p V (Over.mk a)).symm

/-- Lifting original points commutes with every morphism of the lifted tests. -/
lemma liftPointsEquiv_natural (p : X ⟶ S) (V : GroupScheme S)
    (T W : Over S) (b : W ⟶ T) (a : T.left ⟶ X)
    (ha : a ≫ p = T.hom) (x : T ⟶ V.X) :
    liftPointsEquiv p V W (b.left ≫ a)
        (by rw [Category.assoc, ha, Over.w b]) (b ≫ x) =
      (Over.homMk b.left rfl : Over.mk (b.left ≫ a) ⟶ Over.mk a) ≫
        liftPointsEquiv p V T a ha x := by
  apply (baseChangePointsEquiv p V (Over.mk (b.left ≫ a))).injective
  simp only [liftPointsEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    baseChangePointsEquiv_naturality]
  apply Over.OverMorphism.ext
  simp [sourcePointsEquiv, liftedTestIso]

/-- A genuine cover-group comparison and natural upstairs bundle coordinates
construct the lifted all-test charts. -/
def ofCoverIso {W : GroupScheme X}
    (e : (baseChange p).obj V ≅ W)
    (c : ∀ T : Over X, (T ⟶ W.X) ≃*
      Multiplicative (GlobalSections ((Scheme.Modules.pullback T.hom).obj F)))
    (hc : ∀ (T T' : Over X) (b : T' ⟶ T) (x : T ⟶ W.X),
      (c T' (b ≫ x)).toAdd = sectionPullback F b (c T x).toAdd) :
    LiftedModuleCharts p V F where
  equiv T a ha := ((liftPointsEquiv p V T a ha).trans
    (isoPointsEquiv e (Over.mk a))).trans (c (Over.mk a))
  natural T T' b a ha x := by
    let bb : Over.mk (b.left ≫ a) ⟶ Over.mk a := Over.homMk b.left rfl
    change (c (Over.mk (b.left ≫ a))
      (liftPointsEquiv p V T' (b.left ≫ a) _ (b ≫ x) ≫ e.hom.hom.hom)).toAdd = _
    rw [liftPointsEquiv_natural p V T T' b a ha x, Category.assoc]
    have H := hc (Over.mk a) (Over.mk (b.left ≫ a)) bb
      (liftPointsEquiv p V T a ha x ≫ e.hom.hom.hom)
    simpa only [bb, Over.homMk, Over.Hom.left, CostructuredArrow.homMk,
      Over.mk_hom, MulEquiv.trans_apply,
      isoPointsEquiv_apply, sectionPullback, Scheme.Modules.pullbackCongr, eqToIso.hom,
      eqToHom_refl, NatTrans.id_app, Category.comp_id] using H

variable (C : LiftedModuleCharts p V F)

/-- Adding a proved actual linear cocycle compatible with the original point
charts gives the existing module-chart descent interface. -/
def withDatum (D : Datum p F)
    (h : ∀ (T : Over S) (a b : T.left ⟶ X)
      (ha : a ≫ p = T.hom) (hb : b ≫ p = T.hom) (x : T ⟶ V.X),
      (D.θ T.left a b (ha.trans hb.symm)).hom.app ⊤ (C.equiv T a ha x).toAdd =
        (C.equiv T b hb x).toAdd) :
    LinearModuleCharts D V :=
  ⟨C.equiv, C.natural, h⟩

end LiftedModuleCharts
end Langlands.GroupScheme.RelativeUnipotent
