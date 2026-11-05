import Langlands.AlgebraicGeometry.ProjectiveBundle.TensorLineCancellation
import Langlands.AlgebraicGeometry.ProjectiveBundle.TensorLineProjectiveRestriction
import Langlands.AlgebraicGeometry.ProjectiveBundle.FrameAtlasModuleGluing

/-! # The global degree-one comparison for tensoring by a line bundle -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule.RigidifiedModule
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Picard

universe u v w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Scheme.Modules

private lemma iso_hom_of_triple {C : Type v} [Category.{w} C] {W X Y Z : C}
    (e : W ≅ Z) (a : W ≅ X) (b : X ≅ Y) (c : Y ≅ Z)
    (h : e = a ≪≫ b ≪≫ c) :
    e.hom = (a ≪≫ b).hom ≫ c.hom := by
  rw [h]
  simp only [Iso.trans_hom, Category.assoc]

/-- Local comparisons with a common transition give a restriction-compatible ratio. -/
lemma chartComparison_restrict {X U V : Scheme.{u}}
    (jU : U ⟶ X) (jV : V ⟶ X) (r : U ⟶ V) (hr : r ≫ jV = jU)
    {A B : X.Modules} {LU : U.Modules} {LV : V.Modules}
    (aU : (Scheme.Modules.pullback jU).obj A ≅ LU)
    (aV : (Scheme.Modules.pullback jV).obj A ≅ LV)
    (bU : (Scheme.Modules.pullback jU).obj B ≅ LU)
    (bV : (Scheme.Modules.pullback jV).obj B ≅ LV)
    (γ : (Scheme.Modules.pullback r).obj LV ⟶ LU)
    (ha : (Scheme.Modules.pullback r).map aV.hom ≫ γ =
      compHom r jV jU hr A ≫ aU.hom)
    (hb : (Scheme.Modules.pullback r).map bV.hom ≫ γ =
      compHom r jV jU hr B ≫ bU.hom) :
    (Scheme.Modules.pullback r).map (aV ≪≫ bV.symm).hom ≫ compHom r jV jU hr B =
      compHom r jV jU hr A ≫ (aU ≪≫ bU.symm).hom := by
  apply (cancel_mono bU.hom).1
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [← hb]
  rw [← Category.assoc ((Scheme.Modules.pullback r).map bV.inv),
    ← Functor.map_comp]
  simpa using ha

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.ProjectiveBundle.TensorFrames

variable {S : Scheme.{u}} {M N : S.Modules} {n : ℕ}
variable (hM : IsLocallyFreeOfRank M (n + 1)) (hN : IsLocallyFreeRankOne N)

/-- Pullback of the source degree-one module tensored with the original base line. -/
abbrev sourceTensorTwistModule : (tensorAtlas hM hN).bundle.Modules :=
  tensorObj ((Scheme.Modules.pullback (atlasIso hM hN).hom).obj
    ((sourceAtlas hM hN).twistOne hM).obj)
      ((Scheme.Modules.pullback (tensorAtlas hM hN).toBase).obj N)

/-- The source degree-one module times the base line has a standard local form. -/
def sourceTensorTwistChartIso (U : (sourceAtlas hM hN).opens) :
    (Scheme.Modules.pullback (tensorChart hM hN U)).obj
      (sourceTensorTwistModule hM hN) ≅
        (RelativeProjectiveSpace.twistOne U.val.toScheme n).obj :=
  tensorChartContractionIso (tensorChart hM hN U)
    (sourceTwistChartIso hM hN U) (baseLineChartIso hM hN U)

/-- The tensor degree-one transition with its chart schemes explicitly specified. -/
def tensorTwistRestrictionIso
    {U V : (sourceAtlas hM hN).openCover.I₀} (h : U ⟶ V) :
    (Scheme.Modules.pullback (tensorChartRestriction hM hN h)).obj
      (RelativeProjectiveSpace.twistOne V.val.toScheme n).obj ≅
        (RelativeProjectiveSpace.twistOne U.val.toScheme n).obj :=
  (tensorAtlas hM hN).cocycle.chartTwistIso h

/-- The tensor degree-one transition is the source transition followed by the line unit. -/
lemma tensorTwistRestrictionIso_hom
    {U V : (sourceAtlas hM hN).openCover.I₀} (h : U ⟶ V) :
    (tensorTwistRestrictionIso hM hN h).hom =
      (sourceTwistRestrictionIso hM hN h).hom ≫
        (unitAut (RelativeProjectiveSpace.twistOne U.val.toScheme n).obj
          (dualLineProjectiveUnit hM hN h)).hom := by
  have ht := iso_hom_of_triple
    (C := (RelativeProjectiveSpace U.val.toScheme n).Modules)
    (tensorTwistRestrictionIso hM hN h)
    ((Scheme.Modules.pullbackCongr (tensorChartRestriction_eq hM hN h)).app
      (RelativeProjectiveSpace.twistOne V.val.toScheme n).obj)
    ((sourceAtlas hM hN).cocycle.chartTwistIso h)
    (unitAut (RelativeProjectiveSpace.twistOne U.val.toScheme n).obj
      (dualLineProjectiveUnit hM hN h))
    (tensor_chartTwistIso hM hN h)
  exact ht

/-- The source tensor contraction restricts by the actual tensor-atlas transition. -/
lemma sourceTensorTwistChartIso_restrict
    {U V : (sourceAtlas hM hN).openCover.I₀} (h : U ⟶ V) :
    (Scheme.Modules.pullback (tensorChartRestriction hM hN h)).map
        (sourceTensorTwistChartIso hM hN V).hom ≫
          (tensorTwistRestrictionIso hM hN h).hom =
      compHom (tensorChartRestriction hM hN h)
        (tensorChart hM hN V) (tensorChart hM hN U)
        ((tensorAtlas hM hN).cocycle.transition_chart h)
        (sourceTensorTwistModule hM hN) ≫
          (sourceTensorTwistChartIso hM hN U).hom := by
  have hc := tensorChartContractionIso_restrict
    (X := (tensorAtlas hM hN).bundle)
    (U := RelativeProjectiveSpace U.val.toScheme n)
    (V := RelativeProjectiveSpace V.val.toScheme n)
    (tensorChart hM hN U) (tensorChart hM hN V) (tensorChartRestriction hM hN h)
    ((tensorAtlas hM hN).cocycle.transition_chart h)
    (A := (Scheme.Modules.pullback (atlasIso hM hN).hom).obj
      ((sourceAtlas hM hN).twistOne hM).obj)
    (B := (Scheme.Modules.pullback (tensorAtlas hM hN).toBase).obj N)
    (LU := (RelativeProjectiveSpace.twistOne U.val.toScheme n).obj)
    (LV := (RelativeProjectiveSpace.twistOne V.val.toScheme n).obj)
    (sourceTwistChartIso hM hN U) (sourceTwistChartIso hM hN V)
    (baseLineChartIso hM hN U) (baseLineChartIso hM hN V)
    (sourceTwistRestrictionIso hM hN h).hom (dualLineProjectiveUnit hM hN h)
    (sourceTwistChartIso_restrict hM hN h) (baseLineChartIso_restrict hM hN h)
  exact (congrArg
    (fun g => (Scheme.Modules.pullback (tensorChartRestriction hM hN h)).map
      (sourceTensorTwistChartIso hM hN V).hom ≫ g)
    (tensorTwistRestrictionIso_hom hM hN h)).trans hc

/-- The tensor-atlas degree-one module compares locally with the source times the line. -/
def tensorLineTwistChartIso (U : (sourceAtlas hM hN).opens) :
    (Scheme.Modules.pullback (tensorChart hM hN U)).obj
      ((tensorAtlas hM hN).twistOne (isLocallyFreeOfRank_tensor hM hN)).obj ≅
        (Scheme.Modules.pullback (tensorChart hM hN U)).obj
          (sourceTensorTwistModule hM hN) :=
  (tensorAtlas hM hN).twistChartIso (isLocallyFreeOfRank_tensor hM hN) U ≪≫
    (sourceTensorTwistChartIso hM hN U).symm

/-- The corrected local degree-one comparisons commute with every atlas restriction. -/
lemma tensorLineTwistChartIso_restrict
    {U V : (sourceAtlas hM hN).openCover.I₀} (h : U ⟶ V) :
    (Scheme.Modules.pullback (tensorChartRestriction hM hN h)).map
        (tensorLineTwistChartIso hM hN V).hom ≫
      compHom (tensorChartRestriction hM hN h)
        (tensorChart hM hN V) (tensorChart hM hN U)
        ((tensorAtlas hM hN).cocycle.transition_chart h)
        (sourceTensorTwistModule hM hN) =
      compHom (tensorChartRestriction hM hN h)
        (tensorChart hM hN V) (tensorChart hM hN U)
        ((tensorAtlas hM hN).cocycle.transition_chart h)
        ((tensorAtlas hM hN).twistOne (isLocallyFreeOfRank_tensor hM hN)).obj ≫
          (tensorLineTwistChartIso hM hN U).hom := by
  exact chartComparison_restrict
    (tensorChart hM hN U) (tensorChart hM hN V) (tensorChartRestriction hM hN h)
    ((tensorAtlas hM hN).cocycle.transition_chart h)
    ((tensorAtlas hM hN).twistChartIso (isLocallyFreeOfRank_tensor hM hN) U)
    ((tensorAtlas hM hN).twistChartIso (isLocallyFreeOfRank_tensor hM hN) V)
    (sourceTensorTwistChartIso hM hN U) (sourceTensorTwistChartIso hM hN V)
    (tensorTwistRestrictionIso hM hN h).hom
    ((tensorAtlas hM hN).twistChartIso_restrict (isLocallyFreeOfRank_tensor hM hN) h)
    (sourceTensorTwistChartIso_restrict hM hN h)

/-- The joint frame basis is closed under binary intersections. -/
lemma opens_inf (U V : (sourceAtlas hM hN).opens) :
    U.val ⊓ V.val ∈ (tensorAtlas hM hN).opens :=
  opens_of_le U.property inf_le_left

/-- Tensoring a module by a line tensors its degree-one bundle by the base line. -/
def tensorLineTwistIso :
    ((tensorAtlas hM hN).twistOne (isLocallyFreeOfRank_tensor hM hN)).obj ≅
      sourceTensorTwistModule hM hN :=
  (tensorAtlas hM hN).restrictionIso (opens_inf hM hN) _ _
    (tensorLineTwistChartIso hM hN) (tensorLineTwistChartIso_restrict hM hN)

/-- The global tensor-line degree-one isomorphism has the prescribed chart formula. -/
lemma tensorLineTwistIso_local (U : (sourceAtlas hM hN).opens) :
    (Scheme.Modules.pullback (tensorChart hM hN U)).map
      (tensorLineTwistIso hM hN).hom = (tensorLineTwistChartIso hM hN U).hom :=
  (tensorAtlas hM hN).restrictionIso_local (opens_inf hM hN) _ _
    (tensorLineTwistChartIso hM hN) (tensorLineTwistChartIso_restrict hM hN) U

end Langlands.AlgebraicGeometry.ProjectiveBundle.TensorFrames
