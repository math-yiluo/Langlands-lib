import Langlands.AlgebraicGeometry.ProjectiveBundle.TensorLineBaseRestriction
import Langlands.AlgebraicGeometry.ProjectiveBundle.TensorLineTwistRestriction

/-! # Projective restriction of the base-line trivializations -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.SchemeModule.RigidifiedModule
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Picard

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Scheme.Modules

/-- Equal scheme maps have the same canonical structure-module comparison. -/
lemma pullbackCongr_unit {X Y : Scheme.{u}} (a b : X ⟶ Y) (w : a = b) :
    (Scheme.Modules.pullbackCongr w).hom.app (SheafOfModules.unit Y.ringCatSheaf) ≫
        (pullbackUnitIso b).hom = (pullbackUnitIso a).hom := by
  subst w
  simp [Scheme.Modules.pullbackCongr]

/-- Canonical structure-module comparisons commute around a scheme square. -/
lemma squarePullbackIso_unit {X Y X' Y' : Scheme.{u}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (s : X' ⟶ X) (t : Y' ⟶ Y)
    (hs : p' ≫ t = s ≫ p) :
    (squarePullbackIso p p' s t hs (SheafOfModules.unit Y.ringCatSheaf)).hom ≫
        (Scheme.Modules.pullback s).map (pullbackUnitIso p).hom ≫
        (pullbackUnitIso s).hom =
      (Scheme.Modules.pullback p').map (pullbackUnitIso t).hom ≫
        (pullbackUnitIso p').hom := by
  rw [← pullbackUnitComposition _ _ _ s p]
  simp only [squarePullbackIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [pullbackCongr_unit, pullbackUnitComposition]

/-- Canonical structure-module comparisons also carry a unit scalar through a square. -/
lemma squarePullbackIso_unit_scaled {X Y X' Y' : Scheme.{u}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (s : X' ⟶ X) (t : Y' ⟶ Y)
    (hs : p' ≫ t = s ≫ p) (c : Γ(Y', ⊤)ˣ) :
    Langlands.AlgebraicGeometry.LinearSystem.PullbackSquareCompatible p p' s t hs
      (pullbackUnitIso p).hom (pullbackUnitIso p').hom
      ((pullbackUnitIso t).hom ≫ (unitAut (SheafOfModules.unit Y'.ringCatSheaf) c).hom)
      ((pullbackUnitIso s).hom ≫ (unitAut (SheafOfModules.unit X'.ringCatSheaf)
        (Units.map p'.appTop.hom.toMonoidHom c)).hom) := by
  unfold Langlands.AlgebraicGeometry.LinearSystem.PullbackSquareCompatible
  have hm := congrArg Iso.hom
    (pullback_mapIso_unitAut p' (SheafOfModules.unit Y'.ringCatSheaf) c)
  simp only [Functor.map_comp, Category.assoc, Functor.mapIso_hom] at hm ⊢
  rw [hm, unitAut_naturality]
  simpa only [Category.assoc] using congrArg
    (fun f => f ≫ (unitAut (SheafOfModules.unit X'.ringCatSheaf)
      (Units.map p'.appTop.hom.toMonoidHom c)).hom)
    (squarePullbackIso_unit p p' s t hs).symm

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

variable {S X T : Scheme.{u}} {N : S.Modules} {U V : S.Opens}

/-- Pull an actual line chart through a chart of a scheme over the base. -/
def openLinePullbackIso (p : X ⟶ S) (j : T ⟶ X) (b : T ⟶ U.toScheme)
    (h : j ≫ p = b ≫ U.ι) (e : N.restrict U.ι ≅ structureSheaf U.toScheme) :
    (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback p).obj N) ≅
      SheafOfModules.unit T.ringCatSheaf :=
  squarePullbackIso U.ι j b p h N ≪≫
    (Scheme.Modules.pullback b).mapIso (openLineIso e) ≪≫ pullbackUnitIso b

/-- The square construction is the normalized local comparison. -/
lemma openLinePullbackIso_hom_normalize
    (p : X ⟶ S) (j : T ⟶ X) (b : T ⟶ U.toScheme)
    (h : j ≫ p = b ≫ U.ι) (e : N.restrict U.ι ≅ structureSheaf U.toScheme) :
    (openLinePullbackIso p j b h e).hom =
      compHom j p (j ≫ p) rfl N ≫
        (RefinedPullbackComparison.normalize b U.ι (j ≫ p) h.symm
          (openLineIso e)).hom ≫ (pullbackUnitIso b).hom := by
  rw [reassoc_of% (RefinedPullbackComparison.comp_normalize_eq_square
    p j b U.ι h.symm N (openLineIso e))]
  rfl

/-- Original line-chart restriction gives the scalar restriction on every chart above it. -/
lemma openLinePullbackIso_restrict {TU TV : Scheme.{u}}
    (p : X ⟶ S) (jU : TU ⟶ X) (jV : TV ⟶ X) (t : TU ⟶ TV)
    (htj : t ≫ jV = jU) (bU : TU ⟶ U.toScheme) (bV : TV ⟶ V.toScheme)
    (h : U ≤ V) (ht : bU ≫ S.homOfLE h = t ≫ bV)
    (hU : jU ≫ p = bU ≫ U.ι) (hV : jV ≫ p = bV ≫ V.ι)
    (eU : N.restrict U.ι ≅ structureSheaf U.toScheme)
    (eV : N.restrict V.ι ≅ structureSheaf V.toScheme) :
    (Scheme.Modules.pullback t).map (openLinePullbackIso p jV bV hV eV).hom ≫
        (pullbackUnitIso t).hom ≫
          (unitAut (SheafOfModules.unit TU.ringCatSheaf)
            (Units.map bU.appTop.hom.toMonoidHom (openLineTransitionUnit eV eU h))).hom =
      compHom t jV jU htj ((Scheme.Modules.pullback p).obj N) ≫
        (openLinePullbackIso p jU bU hU eU).hom := by
  have he :
      (Scheme.Modules.pullback (S.homOfLE h)).map (openLineIso eV).hom ≫
          ((pullbackUnitIso (S.homOfLE h)).hom ≫
            (unitAut (SheafOfModules.unit U.toScheme.ringCatSheaf)
              (openLineTransitionUnit eV eU h)).hom) =
        compHom (S.homOfLE h) V.ι U.ι (S.homOfLE_ι h) N ≫ (openLineIso eU).hom := by
    simpa only [structureSheaf, openLineRestrictionIso, openPullbackIso, compHom, Iso.trans_hom,
      Functor.mapIso_hom, Iso.app_hom, Category.assoc] using
      congrArg Iso.hom (openLineIso_restrict eV eU h)
  rw [openLinePullbackIso_hom_normalize, openLinePullbackIso_hom_normalize]
  exact RefinedPullbackComparison.normalize_local_restrict_between
    p jU jV t htj bU bV (S.homOfLE h) U.ι V.ι ht hU.symm hV.symm
    (S.homOfLE_ι h) N (openLineIso eU) (openLineIso eV)
    (pullbackUnitIso (S.homOfLE h) ≪≫
      unitAut (SheafOfModules.unit U.toScheme.ringCatSheaf)
        (openLineTransitionUnit eV eU h)) he
    (pullbackUnitIso bU).hom (pullbackUnitIso bV).hom
    ((pullbackUnitIso t).hom ≫
      (unitAut (SheafOfModules.unit TU.ringCatSheaf)
        (Units.map bU.appTop.hom.toMonoidHom (openLineTransitionUnit eV eU h))).hom)
    (squarePullbackIso_unit_scaled bV bU t (S.homOfLE h) ht
      (openLineTransitionUnit eV eU h))

end Langlands.AlgebraicGeometry.ProjectiveBundle

namespace Langlands.AlgebraicGeometry.ProjectiveBundle.TensorFrames

variable {S : Scheme.{u}} {M N : S.Modules} {n : ℕ}
variable (hM : IsLocallyFreeOfRank M (n + 1)) (hN : IsLocallyFreeRankOne N)

/-- The projective transition unit is the pullback of the original line-chart unit. -/
lemma dualLineProjectiveUnit_eq
    {U V : (sourceAtlas hM hN).openCover.I₀} (h : U ⟶ V) :
    dualLineProjectiveUnit hM hN h =
      Units.map (RelativeProjectiveSpace.toBase U.val.toScheme n).appTop.hom.toMonoidHom
        (openLineTransitionUnit V.property.2.some U.property.2.some (leOfHom h)) := by
  unfold dualLineProjectiveUnit
  rw [LinearSystem.scalarsFromBase_comp_toSpecΓ]
  rfl

/-- The actual projective base-line comparisons have the inverse transition scalar. -/
lemma baseLineChartIso_restrict
    {U V : (sourceAtlas hM hN).openCover.I₀} (h : U ⟶ V) :
    (Scheme.Modules.pullback (tensorChartRestriction hM hN h)).map
        (baseLineChartIso hM hN V).hom ≫
      (pullbackUnitIso (tensorChartRestriction hM hN h)).hom ≫
        (unitAut (structureSheaf (RelativeProjectiveSpace U.val.toScheme n))
          (dualLineProjectiveUnit hM hN h)).hom =
      compHom (tensorChartRestriction hM hN h)
        (tensorChart hM hN V) (tensorChart hM hN U)
        ((tensorAtlas hM hN).cocycle.transition_chart h)
        ((Scheme.Modules.pullback (tensorAtlas hM hN).toBase).obj N) ≫
          (baseLineChartIso hM hN U).hom := by
  have ht :
      RelativeProjectiveSpace.toBase U.val.toScheme n ≫ S.homOfLE (leOfHom h) =
        tensorChartRestriction hM hN h ≫ RelativeProjectiveSpace.toBase V.val.toScheme n := by
    simpa only [FrameAtlas.openCover_trans] using
      ((tensorAtlas hM hN).cocycle.chartFunctor_map_toBase h).symm
  rw [dualLineProjectiveUnit_eq]
  exact openLinePullbackIso_restrict
    (tensorAtlas hM hN).toBase (tensorChart hM hN U) (tensorChart hM hN V)
    (tensorChartRestriction hM hN h) ((tensorAtlas hM hN).cocycle.transition_chart h)
    (RelativeProjectiveSpace.toBase U.val.toScheme n)
    (RelativeProjectiveSpace.toBase V.val.toScheme n)
    (leOfHom h) ht ((tensorAtlas hM hN).cocycle.chart_toBase U)
    ((tensorAtlas hM hN).cocycle.chart_toBase V) U.property.2.some V.property.2.some

end Langlands.AlgebraicGeometry.ProjectiveBundle.TensorFrames
