/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicOrdinaryScalarModelBase
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicSourcePresentation
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantChart
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantPresentation

/-! # Direct constant presentation of the ordinary chart source

Source: Stacks Project, Tags 093J and 093M.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective
attribute [local irreducible] completedAdicChangeData completedAdicRing
  directCoefficientMap overDirectMap

attribute [local irreducible] sourceDirectIso
  chartConstantsIso constantAssociatedIso overDirectIso directConstant directCoefficientIso
  finitePerfectAdicAssociatedCoherence

private def sourceChartMap
    (X : Scheme.{t}) (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U)
    {B D : Type (t + 1)} [CommRing B] [CommRing D] (q : B →+* D)
    (N : ModuleCat.{t + 1} D) :
    have := ProEt.sliceDense X W
    (chartFunctor X V U W f B).obj
        ((constantSheaf V.left.smallEtaleTopology (ModuleCat.{t + 1} B)).obj
          ((ModuleCat.restrictScalars q).obj N)) ⟶
      (sheafCompose ((ProEt.topology X).over W) (ModuleCat.restrictScalars.{t + 1} q)).obj
        ((chartFunctor X V U W f D).obj
          ((constantSheaf V.left.smallEtaleTopology (ModuleCat.{t + 1} D)).obj N)) := by
  have := ProEt.sliceDense X W
  have : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology V.left) (ProEt.topology U.left) :=
    ProEt.isContinuous_overPullback U.hom
  let PE := ProEtale.comparisonUpperStar (ModuleCat.{t + 1} D) V.left
  let UB := ProEtale.upperStar (ModuleCat.{t + 1} B) U.hom
  let RB := ProEtale.localizationRestriction (ModuleCat.{t + 1} B) f.left
    (finitePerfectAdicChartArrow_weaklyEtale V U W f)
  let EB := ((ProEt.sliceEquiv X W).sheafCongr ((ProEt.topology X).over W)
    (ProEt.topology W.left) (ModuleCat.{t + 1} B)).inverse
  let βP := normalizationPullbackIso V.left.smallEtaleTopology (toProEt V.left)
    (ProEt.topology V.left) q
  let βU := normalizationPullbackIso (ProEt.topology V.left)
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom) (ProEt.topology U.left) q
  exact (chartFunctor X V U W f B).map
      ((constantCommuteCompose V.left.smallEtaleTopology
        (ModuleCat.restrictScalars.{t + 1} q)).inv.app N) ≫
    (UB ⋙ RB ⋙ EB).map (βP.hom.app
      ((constantSheaf V.left.smallEtaleTopology (ModuleCat.{t + 1} D)).obj N)) ≫
    (RB ⋙ EB).map (βU.hom.app (PE.obj
      ((constantSheaf V.left.smallEtaleTopology (ModuleCat.{t + 1} D)).obj N)))

private lemma sourceChartMap_coefficient
    (X : Scheme.{t}) (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U)
    {B D : Type (t + 1)} [CommRing B] [CommRing D] (q : B →+* D)
    (N : ModuleCat.{t + 1} D) :
    have := ProEt.sliceDense X W
    sourceChartMap X V U W f q N ≫
        (sheafCompose ((ProEt.topology X).over W)
          (ModuleCat.restrictScalars.{t + 1} q)).map
            ((chartConstantsIso X V U W f D).hom.app N) =
      (chartConstantsIso X V U W f B).hom.app
          ((ModuleCat.restrictScalars q).obj N) ≫
        (constantCommuteCompose ((ProEt.topology X).over W)
          (ModuleCat.restrictScalars.{t + 1} q)).inv.app N := by
  have := ProEt.sliceDense X W
  simpa only [sourceChartMap, Category.assoc] using
    chartConstantsIso_coefficient X V U W f q N

attribute [local irreducible] sourceChartMap

private def SourceChartSquare
    (X : Scheme.{t}) (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U)
    {B D : Type (t + 1)} [CommRing B] [CommRing D]
    {R S : Sheaf (ProEt.topology X) RingCat.{t + 1}}
    (α : (Functor.const X.ProEtᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
    (β : (Functor.const X.ProEtᵒᵖ).obj (RingCat.of D) ⟶ S.obj)
    [Presheaf.IsLocallyInjective (ProEt.topology X) α]
    [Presheaf.IsLocallySurjective (ProEt.topology X) α]
    [Presheaf.IsLocallyInjective (ProEt.topology X) β]
    [Presheaf.IsLocallySurjective (ProEt.topology X) β]
    [Presheaf.IsLocallyInjective ((ProEt.topology X).over W)
      (whiskerLeft (Over.forget W).op α)]
    [Presheaf.IsLocallySurjective ((ProEt.topology X).over W)
      (whiskerLeft (Over.forget W).op α)]
    [Presheaf.IsLocallyInjective ((ProEt.topology X).over W)
      (whiskerLeft (Over.forget W).op β)]
    [Presheaf.IsLocallySurjective ((ProEt.topology X).over W)
      (whiskerLeft (Over.forget W).op β)]
    (q : B →+* D) (p : R ⟶ S)
    (h : ∀ Z, α.app Z ≫ p.hom.app Z = RingCat.ofHom q ≫ β.app Z)
    (N : ModuleCat.{t + 1} D) : Prop :=
    have := ProEt.sliceDense X W
    let αs : (Functor.const (Over W)ᵒᵖ).obj (RingCat.of B) ⟶ (R.over W).obj :=
      whiskerLeft (Over.forget W).op α
    let βs : (Functor.const (Over W)ᵒᵖ).obj (RingCat.of D) ⟶ (S.over W).obj :=
      whiskerLeft (Over.forget W).op β
    let ps : R.over W ⟶ S.over W := ((ProEt.topology X).overPullback RingCat.{t + 1} W).map p
    (finitePerfectAdicAssociated αs).map
        ((chartConstantsIso X V U W f B).hom.app ((ModuleCat.restrictScalars q).obj N)) ≫
      (constantAssociatedIso αs).inv.app ((ModuleCat.restrictScalars q).obj N) ≫
      (overDirectIso α W).hom.app ((ModuleCat.restrictScalars q).obj N) ≫
      (SheafOfModules.overFunctor R W).map
        ((directCoefficientIso α β q p h).hom.app N) =
    (finitePerfectAdicAssociated αs).map (sourceChartMap X V U W f q N) ≫
      (finitePerfectAdicAssociatedCoherence αs βs q ps
        (fun Z ↦ h ((Over.forget W).op.obj Z))).hom.app
          ((chartFunctor X V U W f D).obj
            ((constantSheaf V.left.smallEtaleTopology (ModuleCat.{t + 1} D)).obj N)) ≫
      (SheafOfModules.restrictScalars ps).map
        ((finitePerfectAdicAssociated βs).map ((chartConstantsIso X V U W f D).hom.app N) ≫
          (constantAssociatedIso βs).inv.app N ≫ (overDirectIso β W).hom.app N)

private lemma sourceChart_coefficient
    (X : Scheme.{t}) (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U)
    {B D : Type (t + 1)} [CommRing B] [CommRing D]
    {R S : Sheaf (ProEt.topology X) RingCat.{t + 1}}
    (α : (Functor.const X.ProEtᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
    (β : (Functor.const X.ProEtᵒᵖ).obj (RingCat.of D) ⟶ S.obj)
    [Presheaf.IsLocallyInjective (ProEt.topology X) α]
    [Presheaf.IsLocallySurjective (ProEt.topology X) α]
    [Presheaf.IsLocallyInjective (ProEt.topology X) β]
    [Presheaf.IsLocallySurjective (ProEt.topology X) β]
    [Presheaf.IsLocallyInjective ((ProEt.topology X).over W)
      (whiskerLeft (Over.forget W).op α)]
    [Presheaf.IsLocallySurjective ((ProEt.topology X).over W)
      (whiskerLeft (Over.forget W).op α)]
    [Presheaf.IsLocallyInjective ((ProEt.topology X).over W)
      (whiskerLeft (Over.forget W).op β)]
    [Presheaf.IsLocallySurjective ((ProEt.topology X).over W)
      (whiskerLeft (Over.forget W).op β)]
    (q : B →+* D) (p : R ⟶ S)
    (h : ∀ Z, α.app Z ≫ p.hom.app Z = RingCat.ofHom q ≫ β.app Z)
    (N : ModuleCat.{t + 1} D) :
    SourceChartSquare X V U W f α β q p h N := by
  unfold SourceChartSquare
  have := ProEt.sliceDense X W
  exact associatedOverChart_coefficient α β q p h W N
    ((chartConstantsIso X V U W f B).app ((ModuleCat.restrictScalars q).obj N))
    ((chartConstantsIso X V U W f D).app N) (sourceChartMap X V U W f q N)
    (sourceChartMap_coefficient X V U W f q N)

private lemma sourceChart_lifted_section
    (X : Scheme.{t}) (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U)
    {B D : Type t} [CommRing B] [CommRing D]
    {R S : Sheaf (ProEt.topology X) RingCat.{t + 1}}
    (α : (Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{t + 1} B)) ⟶ R.obj)
    (β : (Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{t + 1} D)) ⟶ S.obj)
    [Presheaf.IsLocallyInjective (ProEt.topology X) α]
    [Presheaf.IsLocallySurjective (ProEt.topology X) α]
    [Presheaf.IsLocallyInjective (ProEt.topology X) β]
    [Presheaf.IsLocallySurjective (ProEt.topology X) β]
    [Presheaf.IsLocallyInjective ((ProEt.topology X).over W)
      (whiskerLeft (Over.forget W).op α)]
    [Presheaf.IsLocallySurjective ((ProEt.topology X).over W)
      (whiskerLeft (Over.forget W).op α)]
    [Presheaf.IsLocallyInjective ((ProEt.topology X).over W)
      (whiskerLeft (Over.forget W).op β)]
    [Presheaf.IsLocallySurjective ((ProEt.topology X).over W)
      (whiskerLeft (Over.forget W).op β)]
    (q₀ : B →+* D) (p : R ⟶ S)
    (h : ∀ Z, α.app Z ≫ p.hom.app Z = RingCat.ofHom (RingHom.ulift q₀) ≫ β.app Z)
    (N : ModuleCat.{t} D) :
    have := ProEt.sliceDense X W
    let q := RingHom.ulift q₀
    let MB := (finitePerfectAdicScalarModelLift B).obj ((ModuleCat.restrictScalars q₀).obj N)
    let MD := (finitePerfectAdicScalarModelLift D).obj N
    let αs : (Functor.const (Over W)ᵒᵖ).obj
        (RingCat.of (ULift.{t + 1} B)) ⟶ (R.over W).obj :=
      whiskerLeft (Over.forget W).op α
    let βs : (Functor.const (Over W)ᵒᵖ).obj
        (RingCat.of (ULift.{t + 1} D)) ⟶ (S.over W).obj :=
      whiskerLeft (Over.forget W).op β
    let ps : R.over W ⟶ S.over W :=
      ((ProEt.topology X).overPullback RingCat.{t + 1} W).map p
    ∀ (Z : (Over W)ᵒᵖ)
      (x : ((finitePerfectAdicAssociated αs).obj
        ((constantSheaf V.left.smallEtaleTopology (ModuleCat.{t + 1} (ULift.{t + 1} B)) ⋙
          chartFunctor X V U W f (ULift.{t + 1} B)).obj MB)).val.obj Z),
    ((finitePerfectAdicAssociated αs).map
        ((chartConstantsIso X V U W f (ULift.{t + 1} B)).hom.app MB) ≫
      (constantAssociatedIso αs).inv.app MB ≫ (overDirectIso α W).hom.app MB ≫
      (SheafOfModules.overFunctor R W).map
        ((directCoefficientIso α β q p h).hom.app MD)).val.app Z x =
    ((finitePerfectAdicAssociated αs).map (sourceChartMap X V U W f q MD) ≫
      (finitePerfectAdicAssociatedCoherence αs βs q ps
        (fun Y ↦ h ((Over.forget W).op.obj Y))).hom.app
          ((chartFunctor X V U W f (ULift.{t + 1} D)).obj
            ((constantSheaf V.left.smallEtaleTopology
              (ModuleCat.{t + 1} (ULift.{t + 1} D))).obj MD)) ≫
      (SheafOfModules.restrictScalars ps).map
        ((finitePerfectAdicAssociated βs).map
            ((chartConstantsIso X V U W f (ULift.{t + 1} D)).hom.app MD) ≫
          (constantAssociatedIso βs).inv.app MD ≫ (overDirectIso β W).hom.app MD)).val.app Z x := by
  dsimp only
  have := ProEt.sliceDense X W
  intro Z x
  have H := sourceChart_coefficient X V U W f α β (RingHom.ulift q₀) p h
    ((finitePerfectAdicScalarModelLift D).obj N)
  unfold SourceChartSquare at H
  dsimp only at H
  exact DFunLike.congr_fun
    (congrArg (fun k ↦ (k.val.app Z).hom.toAddMonoidHom) H) x

attribute [local irreducible] SourceChartSquare

private abbrev sourcePost
    (X : Scheme.{t}) (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U)
    {B : Type (t + 1)} [CommRing B]
    {R T : Sheaf ((ProEt.topology X).over W) RingCat.{t + 1}}
    (α : (Functor.const (Over W)ᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
    [Presheaf.IsLocallyInjective ((ProEt.topology X).over W) α]
    [Presheaf.IsLocallySurjective ((ProEt.topology X).over W) α]
    (a : T ⟶ R) :=
  have := ProEt.sliceDense X W
  ProEtale.localizationRestriction (ModuleCat.{t + 1} B) f.left
      (finitePerfectAdicChartArrow_weaklyEtale V U W f) ⋙
    ((ProEt.sliceEquiv X W).sheafCongr ((ProEt.topology X).over W)
      (ProEt.topology W.left) (ModuleCat.{t + 1} B)).inverse ⋙
    finitePerfectAdicAssociated α ⋙ SheafOfModules.restrictScalars a

section PastingFormula
variable
    (X : Scheme.{t}) (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U)
    {B D : Type t} [CommRing B] [CommRing D] (q₀ : B →+* D)
    {R S T : Sheaf ((ProEt.topology X).over W) RingCat.{t + 1}}
    (α : (Functor.const (Over W)ᵒᵖ).obj (RingCat.of (ULift.{t + 1} B)) ⟶ R.obj)
    (β : (Functor.const (Over W)ᵒᵖ).obj (RingCat.of (ULift.{t + 1} D)) ⟶ S.obj)
    [Presheaf.IsLocallyInjective ((ProEt.topology X).over W) α]
    [Presheaf.IsLocallySurjective ((ProEt.topology X).over W) α]
    [Presheaf.IsLocallyInjective ((ProEt.topology X).over W) β]
    [Presheaf.IsLocallySurjective ((ProEt.topology X).over W) β]
    (a : T ⟶ R) (p : R ⟶ S) (c : T ⟶ S)
    (h : ∀ Z, α.app Z ≫ p.hom.app Z = RingCat.ofHom (RingHom.ulift q₀) ≫ β.app Z)

private def sourcePastedStep
    (z : sheafCompose (ProEt.topology U.left)
        (ModuleCat.restrictScalars.{t + 1} (RingHom.ulift q₀)) ⋙
        sourcePost X V U W f α a ≅ sourcePost X V U W f β c)
    :
    ModuleCat.restrictScalars q₀ ⋙ finitePerfectAdicScalarModelLift B ⋙
      constantSheaf V.left.smallEtaleTopology (ModuleCat.{t + 1} (ULift.{t + 1} B)) ⋙
      ProEtale.comparisonUpperStar (ModuleCat.{t + 1} (ULift.{t + 1} B)) V.left ⋙
      ProEtale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} B)) U.hom ⋙
      sourcePost X V U W f α a ≅
    finitePerfectAdicScalarModelLift D ⋙
      constantSheaf V.left.smallEtaleTopology (ModuleCat.{t + 1} (ULift.{t + 1} D)) ⋙
      ProEtale.comparisonUpperStar (ModuleCat.{t + 1} (ULift.{t + 1} D)) V.left ⋙
      ProEtale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} D)) U.hom ⋙
      sourcePost X V U W f β c := by
  have : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology V.left) (ProEt.topology U.left) :=
    ProEt.isContinuous_overPullback U.hom
  let q : ULift.{t + 1} B →+* ULift.{t + 1} D := RingHom.ulift q₀
  let eC := constantCommuteCompose V.left.smallEtaleTopology
    (ModuleCat.restrictScalars.{t + 1} q)
  let eP := normalizationPullbackIso V.left.smallEtaleTopology (toProEt V.left)
    (ProEt.topology V.left) q
  let eU := normalizationPullbackIso (ProEt.topology V.left)
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom) (ProEt.topology U.left) q
  exact finitePerfectAdicPasteCoefficientStep (finitePerfectAdicScalarModelLiftRestrict q₀)
    (finitePerfectAdicPasteCoefficientStep eC.symm
      (finitePerfectAdicPasteCoefficientStep eP
        (finitePerfectAdicPasteCoefficientStep eU z)))

private lemma sourcePastedStep_forget
    (z : sheafCompose (ProEt.topology U.left)
        (ModuleCat.restrictScalars.{t + 1} (RingHom.ulift q₀)) ⋙
        sourcePost X V U W f α a ≅ sourcePost X V U W f β c)
    (hz : ∀ (L : Sheaf (ProEt.topology U.left)
      (ModuleCat.{t + 1} (ULift.{t + 1} D))),
      have := ProEt.sliceDense X W
      let P := (((ProEt.sliceEquiv X W).sheafCongr ((ProEt.topology X).over W)
        (ProEt.topology W.left) (ModuleCat.{t + 1} (ULift.{t + 1} D))).inverse).obj
          ((ProEtale.localizationRestriction (ModuleCat.{t + 1} (ULift.{t + 1} D)) f.left
            (finitePerfectAdicChartArrow_weaklyEtale V U W f)).obj L)
      (SheafOfModules.toSheaf T).map (z.hom.app L) =
        (SheafOfModules.toSheaf R).map
          ((finitePerfectAdicAssociatedCoherence α β (RingHom.ulift q₀) p h).hom.app P))
    (N : ModuleCat.{t} D) :
    have := ProEt.sliceDense X W
    let q : ULift.{t + 1} B →+* ULift.{t + 1} D := RingHom.ulift q₀
    let M := (finitePerfectAdicScalarModelLift D).obj N
    SourceRestrictionFormula a p c
      ((finitePerfectAdicAssociated α).obj
        ((chartFunctor X V U W f (ULift.{t + 1} B)).obj
          ((constantSheaf V.left.smallEtaleTopology
            (ModuleCat.{t + 1} (ULift.{t + 1} B))).obj
              ((finitePerfectAdicScalarModelLift B).obj
                ((ModuleCat.restrictScalars q₀).obj N)))))
      ((finitePerfectAdicAssociated β).obj
        ((chartFunctor X V U W f (ULift.{t + 1} D)).obj
          ((constantSheaf V.left.smallEtaleTopology
            (ModuleCat.{t + 1} (ULift.{t + 1} D))).obj M)))
      ((sourcePastedStep X V U W f q₀ α β a c z).hom.app N)
      ((finitePerfectAdicAssociated α).map (sourceChartMap X V U W f q M) ≫
        (finitePerfectAdicAssociatedCoherence α β q p h).hom.app
          ((chartFunctor X V U W f (ULift.{t + 1} D)).obj
            ((constantSheaf V.left.smallEtaleTopology
              (ModuleCat.{t + 1} (ULift.{t + 1} D))).obj M))) := by
  unfold SourceRestrictionFormula
  dsimp only
  have := ProEt.sliceDense X W
  have : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology V.left) (ProEt.topology U.left) :=
    ProEt.isContinuous_overPullback U.hom
  unfold sourcePastedStep
  simp only [source_lift_paste_app]
  simp only [source_paste_app, Functor.comp_map, Functor.map_comp]
  rw [hz]
  unfold sourcePost sourceChartMap
  dsimp only [chartFunctor, Functor.comp_map, Functor.comp_obj]
  simp only [Functor.map_comp, forget_restrict, Iso.symm_hom, Category.assoc]

end PastingFormula

attribute [local semireducible] directConstant

end AlgebraicGeometry.Scheme
