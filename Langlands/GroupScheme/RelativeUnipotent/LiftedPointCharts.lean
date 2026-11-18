import Langlands.GroupScheme.RelativeUnipotent.LiftedModuleCharts
import Langlands.GroupScheme.RelativeUnipotent.ModulePointComparisons

/-! # Actual point charts over a fixed lift of the base -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.Scheme.Modules.LineBundleFlatDescent
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent.LiftedModuleCharts

variable {S X : Scheme.{u}} {p : X ⟶ S} {V : GroupScheme S} {F : X.Modules}
  (C : LiftedModuleCharts p V F)

/-- Equal actual lifts give the canonical pullback-congruence comparison of
their original point sections. -/
lemma equiv_congr (T : Over S) (a c : T.left ⟶ X)
    (ha : a ≫ p = T.hom) (hc : c ≫ p = T.hom) (h : a = c) (x : T ⟶ V.X) :
    ((Scheme.Modules.pullbackCongr h).hom.app F).app ⊤ (C.equiv T a ha x).toAdd =
      (C.equiv T c hc x).toAdd := by
  subst c
  simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_refl,
    NatTrans.id_app, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]

/-- Naturality with any prescribed composite lift, retaining the exact
canonical comparison for the equality of underlying maps. -/
lemma natural_comp (T W : Over S) (b : W ⟶ T) (a : T.left ⟶ X)
    (ha : a ≫ p = T.hom) (a' : W.left ⟶ X) (ha' : a' ≫ p = W.hom)
    (h : b.left ≫ a = a') (x : T ⟶ V.X) :
    (C.equiv W a' ha' (b ≫ x)).toAdd =
      (compIso b.left a a' h F).hom.app ⊤
        (pullbackSection b.left ((Scheme.Modules.pullback a).obj F)
          (C.equiv T a ha x).toAdd) := by
  have H := C.equiv_congr W (b.left ≫ a) a'
    (by rw [Category.assoc, ha, Over.w b]) ha' h (b ≫ x)
  rw [← H, C.natural]
  rfl

/-- A fixed lift of a base map gives actual natural charts of the original
pullback group into the actual pulled-back module. -/
def atLift {Y : Scheme.{u}} (f : Y ⟶ S) (a : Y ⟶ X) (ha : a ≫ p = f) :
    ModulePointCharts ((GroupScheme.baseChange f).obj V) ((Scheme.Modules.pullback a).obj F) where
  equiv T := (baseChangePointsEquiv f V T).trans
    ((C.equiv ((Over.map f).obj T) (T.hom ≫ a)
      (by rw [Category.assoc, ha]; rfl)).trans
        (AddEquiv.toMultiplicative (baseChangeSectionEquiv a F T).symm))
  natural T W b x := by
    change (baseChangeSectionEquiv a F W).symm
        (C.equiv ((Over.map f).obj W) (W.hom ≫ a) _
          (baseChangePointsEquiv f V W (b ≫ x))).toAdd =
      sectionPullback ((Scheme.Modules.pullback a).obj F) b
        ((baseChangeSectionEquiv a F T).symm
          (C.equiv ((Over.map f).obj T) (T.hom ≫ a) _
            (baseChangePointsEquiv f V T x)).toAdd)
    apply (baseChangeSectionEquiv a F W).injective
    rw [AddEquiv.apply_symm_apply, baseChangeSectionEquiv_naturality,
      AddEquiv.apply_symm_apply, baseChangePointsEquiv_naturality]
    exact C.natural_comp ((Over.map f).obj T) ((Over.map f).obj W)
      ((Over.map f).map b) (T.hom ≫ a) _ (W.hom ≫ a) _
      (by simpa only [Over.map_map_left, Category.assoc] using
        congrArg (fun k => k ≫ a) (Over.w b))
      (baseChangePointsEquiv f V T x)

/-- The fixed-lift chart is exactly the original point chart, normalized by
the original canonical module composition comparison. -/
lemma atLift_apply {Y : Scheme.{u}} (f : Y ⟶ S) (a : Y ⟶ X) (ha : a ≫ p = f)
    (T : Over Y) (x : T ⟶ ((GroupScheme.baseChange f).obj V).X) :
    baseChangeSectionEquiv a F T ((C.atLift f a ha).equiv T x).toAdd =
      (C.equiv ((Over.map f).obj T) (T.hom ≫ a)
        (by rw [Category.assoc, ha]; rfl) (baseChangePointsEquiv f V T x)).toAdd := by
  change (baseChangeSectionEquiv a F T) ((baseChangeSectionEquiv a F T).symm _) = _
  exact AddEquiv.apply_symm_apply _ _

end Langlands.GroupScheme.RelativeUnipotent.LiftedModuleCharts
