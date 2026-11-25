/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantSiteComparison

/-! # Normalized constant module sheaves on the chart -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace AlgebraicGeometry.Scheme

private def comparisonConstantsIso (X : Scheme.{t}) (B : Type (t + 1)) [CommRing B] :
    constantSheaf X.smallEtaleTopology (ModuleCat.{t + 1} B) ⋙
        ProEtale.comparisonUpperStar (ModuleCat.{t + 1} B) X ≅
      constantSheaf (ProEt.topology X) (ModuleCat.{t + 1} B) :=
  constantPullIso X.smallEtaleTopology (ProEt.topology X) (toProEt X)
    (ProEtale.comparisonUpperStar (ModuleCat.{t + 1} B) X)
    (ProEtale.comparisonAdjunction (ModuleCat.{t + 1} B) X)
    (Etale.isTerminalMkId X) ((Etale.isTerminalMkId X).isTerminalObj (toProEt X))

private def upperConstantsIso {X Y : Scheme.{t}} (g : X ⟶ Y)
    (B : Type (t + 1)) [CommRing B] :
    constantSheaf (ProEt.topology Y) (ModuleCat.{t + 1} B) ⋙
        ProEtale.upperStar (ModuleCat.{t + 1} B) g ≅
      constantSheaf (ProEt.topology X) (ModuleCat.{t + 1} B) := by
  let F := MorphismProperty.Over.pullback @WeaklyEtale ⊤ g
  have := ProEt.isContinuous_overPullback g
  exact constantPullIso (ProEt.topology Y) (ProEt.topology X) F
    (ProEtale.upperStar (ModuleCat.{t + 1} B) g)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{t + 1} B) g)
    (Limits.terminalIsTerminal (C := Y.ProEt))
    ((Limits.terminalIsTerminal (C := Y.ProEt)).isTerminalObj F)

private def localizationConstantsIso {X Y : Scheme.{t}} (g : X ⟶ Y)
    (hg : WeaklyEtale g) (B : Type (t + 1)) [CommRing B] :
    constantSheaf (ProEt.topology Y) (ModuleCat.{t + 1} B) ⋙
        ProEtale.localizationRestriction (ModuleCat.{t + 1} B) g hg ≅
      constantSheaf (ProEt.topology X) (ModuleCat.{t + 1} B) :=
  isoWhiskerLeft (Functor.const Y.ProEtᵒᵖ)
    ((MorphismProperty.Over.map ⊤ hg).pushforwardContinuousSheafificationCompatibility
      (ModuleCat.{t + 1} B) (ProEt.topology X) (ProEt.topology Y)).symm

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

private lemma comparisonConstantsIso_coefficient (X : Scheme.{t})
    {B E : Type (t + 1)} [CommRing B] [CommRing E] (q : B →+* E)
    (N : ModuleCat.{t + 1} E) :
    (ProEtale.comparisonUpperStar (ModuleCat.{t + 1} B) X).map
        ((constantCommuteCompose X.smallEtaleTopology
          (ModuleCat.restrictScalars.{t + 1} q)).inv.app N) ≫
      (normalizationPullbackIso X.smallEtaleTopology (toProEt X)
        (ProEt.topology X) q).hom.app
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{t + 1} E)).obj N) ≫
      (sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{t + 1} q)).map
        ((comparisonConstantsIso X E).hom.app N) ≫
      (constantCommuteCompose (ProEt.topology X)
        (ModuleCat.restrictScalars.{t + 1} q)).hom.app N =
    (comparisonConstantsIso X B).hom.app ((ModuleCat.restrictScalars.{t + 1} q).obj N) :=
  constantPull_coefficient X.smallEtaleTopology (ProEt.topology X) (toProEt X)
    (Etale.isTerminalMkId X) ((Etale.isTerminalMkId X).isTerminalObj (toProEt X)) q N

private lemma upperConstantsIso_coefficient {X Y : Scheme.{t}} (g : X ⟶ Y)
    {B E : Type (t + 1)} [CommRing B] [CommRing E] (q : B →+* E)
    (N : ModuleCat.{t + 1} E) :
    have := ProEt.isContinuous_overPullback g
    (ProEtale.upperStar (ModuleCat.{t + 1} B) g).map
        ((constantCommuteCompose (ProEt.topology Y)
          (ModuleCat.restrictScalars.{t + 1} q)).inv.app N) ≫
      (normalizationPullbackIso (ProEt.topology Y)
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) (ProEt.topology X) q).hom.app
        ((constantSheaf (ProEt.topology Y) (ModuleCat.{t + 1} E)).obj N) ≫
      (sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{t + 1} q)).map
        ((upperConstantsIso g E).hom.app N) ≫
      (constantCommuteCompose (ProEt.topology X)
        (ModuleCat.restrictScalars.{t + 1} q)).hom.app N =
    (upperConstantsIso g B).hom.app ((ModuleCat.restrictScalars.{t + 1} q).obj N) := by
  let F := MorphismProperty.Over.pullback @WeaklyEtale ⊤ g
  have := ProEt.isContinuous_overPullback g
  exact constantPull_coefficient (ProEt.topology Y) (ProEt.topology X) F
    (terminalIsTerminal (C := Y.ProEt))
    ((terminalIsTerminal (C := Y.ProEt)).isTerminalObj F) q N

private lemma localizationConstantsIso_inv_unit {X Y : Scheme.{t}} (g : X ⟶ Y)
    (hg : WeaklyEtale g) (B : Type (t + 1)) [CommRing B]
    (N : ModuleCat.{t + 1} B) :
    toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj N) ≫
        ((localizationConstantsIso g hg B).inv.app N).hom =
      whiskerLeft (MorphismProperty.Over.map ⊤ hg).op
        (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj N)) := by
  exact (MorphismProperty.Over.map ⊤ hg).toSheafify_pullbackSheafificationCompatibility
    (ModuleCat.{t + 1} B) (ProEt.topology X) (ProEt.topology Y)
    ((Functor.const Y.ProEtᵒᵖ).obj N)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

private lemma localizationConstantsIso_coefficient {X Y : Scheme.{t}} (g : X ⟶ Y)
    (hg : WeaklyEtale g) {B E : Type (t + 1)} [CommRing B] [CommRing E] (q : B →+* E)
    (N : ModuleCat.{t + 1} E) :
    (ProEtale.localizationRestriction (ModuleCat.{t + 1} B) g hg).map
        ((constantCommuteCompose (ProEt.topology Y)
          (ModuleCat.restrictScalars.{t + 1} q)).inv.app N) ≫
      (sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{t + 1} q)).map
        ((localizationConstantsIso g hg E).hom.app N) ≫
      (constantCommuteCompose (ProEt.topology X)
        (ModuleCat.restrictScalars.{t + 1} q)).hom.app N =
    (localizationConstantsIso g hg B).hom.app
      ((ModuleCat.restrictScalars.{t + 1} q).obj N) := by
  have : (MorphismProperty.Over.map ⊤ hg).IsContinuous
      (ProEt.topology X) (ProEt.topology Y) :=
    ProEt.isContinuous_overMap hg
  exact constantPush_coefficient (ProEt.topology X) (ProEt.topology Y)
    (MorphismProperty.Over.map ⊤ hg) q
    (localizationConstantsIso g hg B) (localizationConstantsIso g hg E)
    (localizationConstantsIso_inv_unit g hg B)
    (constantPush_hom_unit (ProEt.topology X) (ProEt.topology Y)
      (MorphismProperty.Over.map ⊤ hg) (localizationConstantsIso g hg E)
      (localizationConstantsIso_inv_unit g hg E)) N

private def sliceConstantsIso (X : Scheme.{t}) (W : X.ProEt)
    (B : Type (t + 1)) [CommRing B] :
    have := ProEt.sliceDense X W
    constantSheaf (ProEt.topology W.left) (ModuleCat.{t + 1} B) ⋙
        ((ProEt.sliceEquiv X W).sheafCongr ((ProEt.topology X).over W)
          (ProEt.topology W.left) (ModuleCat.{t + 1} B)).inverse ≅
      constantSheaf ((ProEt.topology X).over W) (ModuleCat.{t + 1} B) := by
  have := ProEt.sliceDense X W
  exact isoWhiskerLeft (Functor.const W.left.ProEtᵒᵖ)
    (((ProEt.sliceEquiv X W).functor).pushforwardContinuousSheafificationCompatibility
      (ModuleCat.{t + 1} B) ((ProEt.topology X).over W) (ProEt.topology W.left)).symm

private lemma sliceConstantsIso_inv_unit (X : Scheme.{t}) (W : X.ProEt)
    (B : Type (t + 1)) [CommRing B] (N : ModuleCat.{t + 1} B) :
    have := ProEt.sliceDense X W
    toSheafify ((ProEt.topology X).over W) ((Functor.const (Over W)ᵒᵖ).obj N) ≫
        ((sliceConstantsIso X W B).inv.app N).hom =
      whiskerLeft (ProEt.sliceEquiv X W).functor.op
        (toSheafify (ProEt.topology W.left) ((Functor.const W.left.ProEtᵒᵖ).obj N)) := by
  have := ProEt.sliceDense X W
  exact (ProEt.sliceEquiv X W).functor.toSheafify_pullbackSheafificationCompatibility
    (ModuleCat.{t + 1} B) ((ProEt.topology X).over W) (ProEt.topology W.left)
    ((Functor.const W.left.ProEtᵒᵖ).obj N)

private lemma sliceConstantsIso_coefficient (X : Scheme.{t}) (W : X.ProEt)
    {B E : Type (t + 1)} [CommRing B] [CommRing E] (q : B →+* E)
    (N : ModuleCat.{t + 1} E) :
    have := ProEt.sliceDense X W
    let FB := ((ProEt.sliceEquiv X W).sheafCongr ((ProEt.topology X).over W)
      (ProEt.topology W.left) (ModuleCat.{t + 1} B)).inverse
    FB.map ((constantCommuteCompose (ProEt.topology W.left)
          (ModuleCat.restrictScalars.{t + 1} q)).inv.app N) ≫
      (sheafCompose ((ProEt.topology X).over W)
        (ModuleCat.restrictScalars.{t + 1} q)).map ((sliceConstantsIso X W E).hom.app N) ≫
      (constantCommuteCompose ((ProEt.topology X).over W)
        (ModuleCat.restrictScalars.{t + 1} q)).hom.app N =
    (sliceConstantsIso X W B).hom.app ((ModuleCat.restrictScalars.{t + 1} q).obj N) := by
  have := ProEt.sliceDense X W
  exact constantPush_coefficient ((ProEt.topology X).over W) (ProEt.topology W.left)
    (ProEt.sliceEquiv X W).functor q (sliceConstantsIso X W B) (sliceConstantsIso X W E)
    (sliceConstantsIso_inv_unit X W B)
    (constantPush_hom_unit ((ProEt.topology X).over W) (ProEt.topology W.left)
      (ProEt.sliceEquiv X W).functor (sliceConstantsIso X W E)
      (sliceConstantsIso_inv_unit X W E)) N

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] comparisonConstantsIso upperConstantsIso
  localizationConstantsIso sliceConstantsIso

private abbrev chartFunctor
    (X : Scheme.{t}) (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (B : Type (t + 1)) [CommRing B] :=
  have := ProEt.sliceDense X W
  ProEtale.comparisonUpperStar (ModuleCat.{t + 1} B) V.left ⋙
    ProEtale.upperStar (ModuleCat.{t + 1} B) U.hom ⋙
    ProEtale.localizationRestriction (ModuleCat.{t + 1} B) f.left
      (finitePerfectAdicChartArrow_weaklyEtale V U W f) ⋙
    ((ProEt.sliceEquiv X W).sheafCongr ((ProEt.topology X).over W)
      (ProEt.topology W.left) (ModuleCat.{t + 1} B)).inverse

private def chartConstantsIso
    (X : Scheme.{t}) (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (B : Type (t + 1)) [CommRing B] :
    have := ProEt.sliceDense X W
    constantSheaf V.left.smallEtaleTopology (ModuleCat.{t + 1} B) ⋙
        chartFunctor X V U W f B ≅
      constantSheaf ((ProEt.topology X).over W) (ModuleCat.{t + 1} B) := by
  have := ProEt.sliceDense X W
  let D := ModuleCat.{t + 1} B
  let E := ((ProEt.sliceEquiv X W).sheafCongr ((ProEt.topology X).over W)
    (ProEt.topology W.left) D).inverse
  let R := ProEtale.localizationRestriction D f.left
    (finitePerfectAdicChartArrow_weaklyEtale V U W f)
  exact isoWhiskerRight (isoWhiskerRight (isoWhiskerRight
    (comparisonConstantsIso V.left B) (ProEtale.upperStar D U.hom)) R) E ≪≫
    isoWhiskerRight (isoWhiskerRight (upperConstantsIso (X := U.left) (Y := V.left) U.hom B) R) E ≪≫
    isoWhiskerRight (localizationConstantsIso (X := W.left) (Y := U.left) f.left
      (finitePerfectAdicChartArrow_weaklyEtale V U W f) B) E ≪≫ sliceConstantsIso X W B

attribute [local irreducible] chartConstantsIso

-- Four inverse-image comparisons and their sheafification instances are pasted here.
private lemma chartConstantsIso_coefficient
    (X : Scheme.{t}) (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U)
    {B E : Type (t + 1)} [CommRing B] [CommRing E] (q : B →+* E)
    (N : ModuleCat.{t + 1} E) :
    have := ProEt.sliceDense X W
    have : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom).IsContinuous
        (ProEt.topology V.left) (ProEt.topology U.left) :=
      ProEt.isContinuous_overPullback U.hom
    let PE := ProEtale.comparisonUpperStar (ModuleCat.{t + 1} E) V.left
    let UB := ProEtale.upperStar (ModuleCat.{t + 1} B) U.hom
    let RB := ProEtale.localizationRestriction (ModuleCat.{t + 1} B) f.left
      (finitePerfectAdicChartArrow_weaklyEtale V U W f)
    let EB := ((ProEt.sliceEquiv X W).sheafCongr ((ProEt.topology X).over W)
      (ProEt.topology W.left) (ModuleCat.{t + 1} B)).inverse
    let βP := normalizationPullbackIso V.left.smallEtaleTopology (toProEt V.left)
      (ProEt.topology V.left) q
    let βU := normalizationPullbackIso (ProEt.topology V.left)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom) (ProEt.topology U.left) q
    let M := (constantSheaf V.left.smallEtaleTopology (ModuleCat.{t + 1} E)).obj N
    (chartFunctor X V U W f B).map
        ((constantCommuteCompose V.left.smallEtaleTopology
          (ModuleCat.restrictScalars.{t + 1} q)).inv.app N) ≫
      (UB ⋙ RB ⋙ EB).map (βP.hom.app M) ≫
      (RB ⋙ EB).map (βU.hom.app (PE.obj M)) ≫
      (sheafCompose ((ProEt.topology X).over W)
        (ModuleCat.restrictScalars.{t + 1} q)).map ((chartConstantsIso X V U W f E).hom.app N) =
    (chartConstantsIso X V U W f B).hom.app
        ((ModuleCat.restrictScalars.{t + 1} q).obj N) ≫
      (constantCommuteCompose ((ProEt.topology X).over W)
        (ModuleCat.restrictScalars.{t + 1} q)).inv.app N  := by
  have := ProEt.sliceDense X W
  have : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology V.left) (ProEt.topology U.left) :=
    ProEt.isContinuous_overPullback U.hom
  let Q := ModuleCat.restrictScalars.{t + 1} q
  let PB := ProEtale.comparisonUpperStar (ModuleCat.{t + 1} B) V.left
  let PE := ProEtale.comparisonUpperStar (ModuleCat.{t + 1} E) V.left
  let UB := ProEtale.upperStar (ModuleCat.{t + 1} B) U.hom
  let UE := ProEtale.upperStar (ModuleCat.{t + 1} E) U.hom
  let RB := ProEtale.localizationRestriction (ModuleCat.{t + 1} B) f.left
    (finitePerfectAdicChartArrow_weaklyEtale V U W f)
  let RE := ProEtale.localizationRestriction (ModuleCat.{t + 1} E) f.left
    (finitePerfectAdicChartArrow_weaklyEtale V U W f)
  let EB := ((ProEt.sliceEquiv X W).sheafCongr ((ProEt.topology X).over W)
    (ProEt.topology W.left) (ModuleCat.{t + 1} B)).inverse
  let EE := ((ProEt.sliceEquiv X W).sheafCongr ((ProEt.topology X).over W)
    (ProEt.topology W.left) (ModuleCat.{t + 1} E)).inverse
  let βP := (normalizationPullbackIso V.left.smallEtaleTopology (toProEt V.left)
    (ProEt.topology V.left) q).hom
  let βU := (normalizationPullbackIso (ProEt.topology V.left)
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom) (ProEt.topology U.left) q).hom
  let ePB := comparisonConstantsIso V.left B
  let ePE := comparisonConstantsIso V.left E
  let eUB := upperConstantsIso (X := U.left) (Y := V.left) U.hom B
  let eUE := upperConstantsIso (X := U.left) (Y := V.left) U.hom E
  let eRB := localizationConstantsIso (X := W.left) (Y := U.left) f.left
    (finitePerfectAdicChartArrow_weaklyEtale V U W f) B
  let eRE := localizationConstantsIso (X := W.left) (Y := U.left) f.left
    (finitePerfectAdicChartArrow_weaklyEtale V U W f) E
  let eEB := sliceConstantsIso X W B
  let eEE := sliceConstantsIso X W E
  have hP (M : ModuleCat.{t + 1} E) :
      PB.map ((constantCommuteCompose V.left.smallEtaleTopology Q).inv.app M) ≫
        βP.app ((constantSheaf V.left.smallEtaleTopology (ModuleCat.{t + 1} E)).obj M) ≫
        (sheafCompose (ProEt.topology V.left) Q).map (ePE.hom.app M) =
      ePB.hom.app (Q.obj M) ≫
        (constantCommuteCompose (ProEt.topology V.left) Q).inv.app M := by
    apply ((constantCommuteCompose (ProEt.topology V.left) Q).app M).eq_comp_inv.mpr
    erw [Iso.app_hom]
    simpa only [PB, PE, βP, ePE, ePB, Q, Category.assoc] using
      comparisonConstantsIso_coefficient V.left q M
  have hU (M : ModuleCat.{t + 1} E) :
      UB.map ((constantCommuteCompose (ProEt.topology V.left) Q).inv.app M) ≫
        βU.app ((constantSheaf (ProEt.topology V.left) (ModuleCat.{t + 1} E)).obj M) ≫
        (sheafCompose (ProEt.topology U.left) Q).map (eUE.hom.app M) =
      eUB.hom.app (Q.obj M) ≫
        (constantCommuteCompose (ProEt.topology U.left) Q).inv.app M := by
    apply ((constantCommuteCompose (ProEt.topology U.left) Q).app M).eq_comp_inv.mpr
    erw [Iso.app_hom]
    simpa only [UB, UE, βU, eUE, eUB, Q, Category.assoc] using
      upperConstantsIso_coefficient (X := U.left) (Y := V.left) U.hom q M
  let ePUB := isoWhiskerRight ePB UB ≪≫ eUB
  let ePUE := isoWhiskerRight ePE UE ≪≫ eUE
  let βPU := whiskerRight βP UB ≫ whiskerLeft PE βU
  have hPU M := constantCoefficient_comp V.left.smallEtaleTopology (ProEt.topology V.left)
    (ProEt.topology U.left) q PB PE UB UE βP βU ePB ePE eUB eUE hP hU M
  let βR : sheafCompose (ProEt.topology U.left) Q ⋙ RB ⟶
      RE ⋙ sheafCompose (ProEt.topology W.left) Q := 𝟙 _
  have hR (M : ModuleCat.{t + 1} E) :
      RB.map ((constantCommuteCompose (ProEt.topology U.left) Q).inv.app M) ≫
        βR.app ((constantSheaf (ProEt.topology U.left) (ModuleCat.{t + 1} E)).obj M) ≫
        (sheafCompose (ProEt.topology W.left) Q).map (eRE.hom.app M) =
      eRB.hom.app (Q.obj M) ≫
        (constantCommuteCompose (ProEt.topology W.left) Q).inv.app M := by
    apply ((constantCommuteCompose (ProEt.topology W.left) Q).app M).eq_comp_inv.mpr
    dsimp only [βR, NatTrans.id_app]
    erw [Iso.app_hom, Category.id_comp]
    simpa only [RB, RE, eRE, eRB, Q, Category.assoc] using
      localizationConstantsIso_coefficient (X := W.left) (Y := U.left) f.left
        (finitePerfectAdicChartArrow_weaklyEtale V U W f) q M
  have hPUR M := constantCoefficient_comp V.left.smallEtaleTopology (ProEt.topology U.left)
    (ProEt.topology W.left) q (PB ⋙ UB) (PE ⋙ UE) RB RE βPU βR
    ePUB ePUE eRB eRE (by
      intro M
      simpa only [βPU, ePUB, ePUE, Iso.trans_hom, Functor.isoWhiskerRight_hom,
        NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.comp_map, Category.assoc] using hPU M) (by simpa using hR) M
  let ePURB := isoWhiskerRight ePUB RB ≪≫ eRB
  let ePURE := isoWhiskerRight ePUE RE ≪≫ eRE
  let βPUR := whiskerRight βPU RB ≫ whiskerLeft (PE ⋙ UE) βR
  let βE : sheafCompose (ProEt.topology W.left) Q ⋙ EB ⟶
      EE ⋙ sheafCompose ((ProEt.topology X).over W) Q := 𝟙 _
  have hE (M : ModuleCat.{t + 1} E) :
      EB.map ((constantCommuteCompose (ProEt.topology W.left) Q).inv.app M) ≫
        βE.app ((constantSheaf (ProEt.topology W.left) (ModuleCat.{t + 1} E)).obj M) ≫
        (sheafCompose ((ProEt.topology X).over W) Q).map (eEE.hom.app M) =
      eEB.hom.app (Q.obj M) ≫
        (constantCommuteCompose ((ProEt.topology X).over W) Q).inv.app M := by
    apply ((constantCommuteCompose ((ProEt.topology X).over W) Q).app M).eq_comp_inv.mpr
    dsimp only [βE, NatTrans.id_app]
    erw [Iso.app_hom, Category.id_comp]
    simpa only [EB, EE, eEE, eEB, Q, Category.assoc] using
      sliceConstantsIso_coefficient X W q M
  have h := constantCoefficient_comp V.left.smallEtaleTopology (ProEt.topology W.left)
    ((ProEt.topology X).over W) q (PB ⋙ UB ⋙ RB) (PE ⋙ UE ⋙ RE) EB EE βPUR βE
    ePURB ePURE eEB eEE (by
      intro M
      simpa only [βPUR, ePURB, ePURE, Iso.trans_hom, Functor.isoWhiskerRight_hom,
        NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.comp_map, Category.assoc] using hPUR M)
    (by simpa using hE) N
  dsimp only [βPUR, βPU, βR, βE, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, NatTrans.id_app] at h
  erw [EB.map_comp] at h
  simp only [Functor.map_comp, Functor.comp_map, Category.assoc] at h
  erw [EB.map_id, Category.id_comp, Category.id_comp] at h
  simpa only [chartConstantsIso, chartFunctor, ePURB, ePURE, ePUB, ePUE, βPUR, βPU, βR, βE,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, NatTrans.comp_app, Functor.comp_map, Functor.map_comp,
    NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    Category.assoc] using h

end AlgebraicGeometry.Scheme
