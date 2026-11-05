import Langlands.AlgebraicGeometry.ProjectiveBundle.TensorLineTwistCharts
import Langlands.AlgebraicGeometry.Modules.SquarePullbackComparison
import Langlands.AlgebraicGeometry.Modules.SerreVanishing.Mul

/-! # Restriction laws for the tensor-line degree-one comparisons -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule.RigidifiedModule
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Picard

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Scheme.Modules

/-- Equality of restriction maps transports the canonical comparison square. -/
lemma local_restrict_congr {Y U V : Scheme.{u}}
    (r s : U ⟶ V) (w : r = s) (kU : U ⟶ Y) (kV : V ⟶ Y)
    (hr : r ≫ kV = kU) (hs : s ≫ kV = kU) (G : Y.Modules)
    {LU : U.Modules} {LV : V.Modules}
    (eU : (Scheme.Modules.pullback kU).obj G ⟶ LU)
    (eV : (Scheme.Modules.pullback kV).obj G ⟶ LV)
    (γ : (Scheme.Modules.pullback s).obj LV ⟶ LU)
    (he : (Scheme.Modules.pullback s).map eV ≫ γ = compHom s kV kU hs G ≫ eU) :
    (Scheme.Modules.pullback r).map eV ≫
        (Scheme.Modules.pullbackCongr w).hom.app LV ≫ γ =
      compHom r kV kU hr G ≫ eU := by
  subst w
  simpa [Scheme.Modules.pullbackCongr] using he

/-- Transported restriction compatibility also respects a composite pullback. -/
lemma compHom_local_restrict_congr {X Y U V : Scheme.{u}}
    (F : X ⟶ Y) (jU : U ⟶ X) (jV : V ⟶ X) (r s : U ⟶ V)
    (w : r = s) (hr : r ≫ jV = jU) (kU : U ⟶ Y) (kV : V ⟶ Y)
    (hU : jU ≫ F = kU) (hV : jV ≫ F = kV)
    (hk : r ≫ kV = kU) (hs : s ≫ kV = kU)
    (G : Y.Modules) {LU : U.Modules} {LV : V.Modules}
    (eU : (Scheme.Modules.pullback kU).obj G ⟶ LU)
    (eV : (Scheme.Modules.pullback kV).obj G ⟶ LV)
    (γ : (Scheme.Modules.pullback s).obj LV ⟶ LU)
    (he : (Scheme.Modules.pullback s).map eV ≫ γ =
      compHom s kV kU hs G ≫ eU) :
    (Scheme.Modules.pullback r).map (compHom jV F kV hV G ≫ eV) ≫
        (Scheme.Modules.pullbackCongr w).hom.app LV ≫ γ =
      compHom r jV jU hr ((Scheme.Modules.pullback F).obj G) ≫
        compHom jU F kU hU G ≫ eU := by
  exact compHom_local_restrict F jU jV r hr kU kV hU hV hk G eU eV
    ((Scheme.Modules.pullbackCongr w).hom.app LV ≫ γ)
    (local_restrict_congr r s w kU kV hk hs G eU eV γ he)

/-- The isomorphism form keeps the two local composite comparisons explicit. -/
lemma compIso_local_restrict_congr {X Y U V : Scheme.{u}}
    (F : X ⟶ Y) (jU : U ⟶ X) (jV : V ⟶ X) (r s : U ⟶ V)
    (w : r = s) (hr : r ≫ jV = jU) (kU : U ⟶ Y) (kV : V ⟶ Y)
    (hU : jU ≫ F = kU) (hV : jV ≫ F = kV)
    (hk : r ≫ kV = kU) (hs : s ≫ kV = kU)
    (G : Y.Modules) {LU : U.Modules} {LV : V.Modules}
    (eU : (Scheme.Modules.pullback kU).obj G ≅ LU)
    (eV : (Scheme.Modules.pullback kV).obj G ≅ LV)
    (γ : (Scheme.Modules.pullback s).obj LV ≅ LU)
    (he : (Scheme.Modules.pullback s).map eV.hom ≫ γ.hom =
      compHom s kV kU hs G ≫ eU.hom) :
    (Scheme.Modules.pullback r).map (compIso jV F kV hV G ≪≫ eV).hom ≫
        ((Scheme.Modules.pullbackCongr w).app LV ≪≫ γ).hom =
      compHom r jV jU hr ((Scheme.Modules.pullback F).obj G) ≫
        (compIso jU F kU hU G ≪≫ eU).hom := by
  simpa only [Iso.trans_hom, compIso_hom, Iso.app_hom] using
    compHom_local_restrict_congr F jU jV r s w hr kU kV hU hV hk hs G
      eU.hom eV.hom γ.hom he

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.ProjectiveBundle.TensorFrames

variable {S : Scheme.{u}} {M N : S.Modules} {n : ℕ}
variable (hM : IsLocallyFreeOfRank M (n + 1)) (hN : IsLocallyFreeRankOne N)

/-- The tensor chart with its source scheme explicitly specified. -/
abbrev tensorChart (U : (sourceAtlas hM hN).opens) :
    RelativeProjectiveSpace U.val.toScheme n ⟶ (tensorAtlas hM hN).bundle :=
  (tensorAtlas hM hN).cocycle.chart U

/-- The source chart with its source scheme explicitly specified. -/
abbrev sourceChart (U : (sourceAtlas hM hN).opens) :
    RelativeProjectiveSpace U.val.toScheme n ⟶ (sourceAtlas hM hN).bundle :=
  (sourceAtlas hM hN).cocycle.chart U

/-- The source chart comparison with the explicit chart scheme. -/
def sourceChartTwistIso (U : (sourceAtlas hM hN).opens) :
    (Scheme.Modules.pullback (sourceChart hM hN U)).obj
      ((sourceAtlas hM hN).twistOne hM).obj ≅
        (RelativeProjectiveSpace.twistOne U.val.toScheme n).obj :=
  (sourceAtlas hM hN).twistChartIso hM U

/-- The actual tensor restriction, with its chart schemes explicit. -/
abbrev tensorChartRestriction {U V : (sourceAtlas hM hN).openCover.I₀} (h : U ⟶ V) :
    RelativeProjectiveSpace U.val.toScheme n ⟶ RelativeProjectiveSpace V.val.toScheme n :=
  (tensorAtlas hM hN).cocycle.chartFunctor.map h

/-- The explicit tensor chart restriction is the actual source restriction. -/
lemma tensorChartRestriction_eq {U V : (sourceAtlas hM hN).openCover.I₀} (h : U ⟶ V) :
    tensorChartRestriction hM hN h =
      (show RelativeProjectiveSpace U.val.toScheme n ⟶ RelativeProjectiveSpace V.val.toScheme n
        from (sourceAtlas hM hN).cocycle.chartFunctor.map h) :=
  chartFunctor_map_eq hM hN h

/-- Source degree-one transition on the actual tensor-chart restriction map. -/
def sourceTwistRestrictionIso {U V : (sourceAtlas hM hN).openCover.I₀} (h : U ⟶ V) :
    (Scheme.Modules.pullback (tensorChartRestriction hM hN h)).obj
      (RelativeProjectiveSpace.twistOne V.val.toScheme n).obj ≅
        (RelativeProjectiveSpace.twistOne U.val.toScheme n).obj :=
  (Scheme.Modules.pullbackCongr (tensorChartRestriction_eq hM hN h)).app
    (RelativeProjectiveSpace.twistOne V.val.toScheme n).obj ≪≫
      (sourceAtlas hM hN).cocycle.chartTwistIso h

/-- The source chart comparison has the canonical composite morphism. -/
lemma sourceTwistChartIso_hom (U : (sourceAtlas hM hN).opens) :
    (sourceTwistChartIso hM hN U).hom =
      compHom (tensorChart hM hN U) (atlasIso hM hN).hom
        (sourceChart hM hN U) (chart_atlasIso_hom hM hN U)
        ((sourceAtlas hM hN).twistOne hM).obj ≫
          (sourceChartTwistIso hM hN U).hom := by
  unfold sourceTwistChartIso
  rw [Iso.trans_hom, compIso_hom]
  rfl

/-- The source restriction comparison has the transported transition morphism. -/
lemma sourceTwistRestrictionIso_hom
    {U V : (sourceAtlas hM hN).openCover.I₀} (h : U ⟶ V) :
    (sourceTwistRestrictionIso hM hN h).hom =
      (Scheme.Modules.pullbackCongr (tensorChartRestriction_eq hM hN h)).hom.app
        (RelativeProjectiveSpace.twistOne V.val.toScheme n).obj ≫
          ((sourceAtlas hM hN).cocycle.chartTwistIso h).hom := by
  unfold sourceTwistRestrictionIso
  rw [Iso.trans_hom, Iso.app_hom]

/-- The source local comparison commutes with every actual atlas restriction. -/
lemma sourceTwistChartIso_restrict
    {U V : (sourceAtlas hM hN).openCover.I₀} (h : U ⟶ V) :
    (Scheme.Modules.pullback (tensorChartRestriction hM hN h)).map
        (sourceTwistChartIso hM hN V).hom ≫ (sourceTwistRestrictionIso hM hN h).hom =
      compHom (tensorChartRestriction hM hN h)
        (tensorChart hM hN V) (tensorChart hM hN U)
        ((tensorAtlas hM hN).cocycle.transition_chart h)
        ((Scheme.Modules.pullback (atlasIso hM hN).hom).obj
          ((sourceAtlas hM hN).twistOne hM).obj) ≫
        (sourceTwistChartIso hM hN U).hom := by
  rw [sourceTwistChartIso_hom, sourceTwistRestrictionIso_hom, sourceTwistChartIso_hom]
  exact compHom_local_restrict_congr
    (atlasIso hM hN).hom (tensorChart hM hN U) (tensorChart hM hN V)
    (tensorChartRestriction hM hN h)
    (show RelativeProjectiveSpace U.val.toScheme n ⟶ RelativeProjectiveSpace V.val.toScheme n
      from (sourceAtlas hM hN).cocycle.chartFunctor.map h)
    (tensorChartRestriction_eq hM hN h)
    ((tensorAtlas hM hN).cocycle.transition_chart h)
    (sourceChart hM hN U) (sourceChart hM hN V)
    (chart_atlasIso_hom hM hN U) (chart_atlasIso_hom hM hN V)
    ((sourceCartesianAtlas hM hN).compatible h)
    ((sourceAtlas hM hN).cocycle.transition_chart h)
    ((sourceAtlas hM hN).twistOne hM).obj
    (sourceChartTwistIso hM hN U).hom (sourceChartTwistIso hM hN V).hom
    ((sourceAtlas hM hN).cocycle.chartTwistIso h).hom
    ((sourceAtlas hM hN).twistChartIso_restrict hM h)

end Langlands.AlgebraicGeometry.ProjectiveBundle.TensorFrames
