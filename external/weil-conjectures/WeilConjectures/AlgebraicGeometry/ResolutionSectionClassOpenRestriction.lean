/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.RestrictedResolutionOpenCohomology

/-! # Open restriction of the normalized resolution class

Source: Stacks Project, Tags 01E4 and 01FB.
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives
attribute [local irreducible] moduleCohomologyFMap sectionCohomologyTheta
  resolutionSectionClass

set_option backward.defeqAttrib.useBackward true in
private theorem sectionClass_open_restriction {Y : Scheme.{u}}
    (L : CochainComplex Y.Modules ℕ) (U V : Y.Opens) (e : V ≤ U) (p : ℕ) :
    let E := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj
    let A := ((SheafOfModules.forget Y.ringCatSheaf).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj L
    let ev := CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}
    let r := (NatTrans.mapHomologicalComplex
      (Functor.whiskerLeft (SheafOfModules.forget Y.ringCatSheaf ⋙ E)
        (ev.map (homOfLE e).op))
      (ComplexShape.up ℕ)).app L
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map r ≫
      ((A.sc p).mapHomologyIso (E ⋙ ev.obj (op V))).hom ≫
      (E.map (sectionCohomologyTheta L p)).app (op V) =
    ((A.sc p).mapHomologyIso (E ⋙ ev.obj (op U))).hom ≫
      (E.map (sectionCohomologyTheta L p)).app (op U) ≫
      (L.homology p).presheaf.map (homOfLE e).op := by
  dsimp only
  let E := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj
  let A := ((SheafOfModules.forget Y.ringCatSheaf).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj L
  let ev := CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}
  let τ := Functor.whiskerLeft E (ev.map (homOfLE e).op)
  have ht := NatTrans.app_homology τ (A.sc p)
  have hn := (E.map (sectionCohomologyTheta L p)).naturality
    (homOfLE e).op
  let r := (NatTrans.mapHomologicalComplex
    (Functor.whiskerLeft (SheafOfModules.forget Y.ringCatSheaf ⋙ E)
      (ev.map (homOfLE e).op))
    (ComplexShape.up ℕ)).app L
  have hc :
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map r ≫
        ((A.sc p).mapHomologyIso (E ⋙ ev.obj (op V))).hom =
      ((A.sc p).mapHomologyIso (E ⋙ ev.obj (op U))).hom ≫
        (E.obj (A.homology p)).map (homOfLE e).op := by
    rw [← cancel_epi ((A.sc p).mapHomologyIso (E ⋙ ev.obj (op U))).inv]
    simp only [Iso.inv_hom_id_assoc]
    have hr : (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u}
        (ComplexShape.up ℕ) p).map r = (A.sc p).mapNatTrans τ := by
      ext <;> rfl
    change _ ≫ ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u}
        (ComplexShape.up ℕ) p).map r) ≫ _ = _
    rw [hr]
    exact ht.symm
  rw [← Category.assoc, hc, Category.assoc]
  exact congrArg
    (fun t ↦ ((A.sc p).mapHomologyIso (E ⋙ ev.obj (op U))).hom ≫ t) hn

/-- Restrict derived module sections between two opens of the same scheme.
The coefficient identification is restriction composition, with the inclusion equation.
Source: Stacks Project, Tag 01FB.
(blueprint: new-resolution-section-class-open-restriction) -/
def cohomologyOpenRestriction {Y : Scheme.{u}} (G : Y.Modules)
    (U L : Y.Opens) (e : L ≤ U) (p : ℕ) :
    (forget₂ _ AddCommGrpCat.{u}).obj
      ((RingedSpace.moduleCohomology U.toScheme.toRingedSpace p).obj
        ((restrictFunctor U.ι).obj G)) ⟶
    (forget₂ _ AddCommGrpCat.{u}).obj
      ((RingedSpace.moduleCohomology L.toScheme.toRingedSpace p).obj
        ((restrictFunctor L.ι).obj G)) :=
  let j := Y.homOfLE e
  let c := (restrictFunctorComp j U.ι).symm.app G ≪≫
    (restrictFunctorCongr (Y.homOfLE_ι e)).app G
  moduleCohomologyFMap j
    ((restrictAdjunction j).unit.app ((restrictFunctor U.ι).obj G) ≫
      (pushforward j).map c.hom) p

set_option backward.defeqAttrib.useBackward true in
/-- The normalized resolution class commutes with restriction between arbitrary opens.
No affineness, quasi-coherence, base change or scalar extension is assumed.
Source: Stacks Project, Tag 01E4, Lemma 20.7.3; Tag 01FB, Remark 20.14.2.
(blueprint: new-resolution-section-class-open-restriction)

Proof: Substitute U = f inverse V. Apply restrictedResolution_open_cohomology
to the two inverse-image opens and the pinned identifications R and R'. The
termwise restriction of I's sections equals the restriction of the pushed
complex K's sections, degreewise by reflexivity. Expand resolutionSectionClass
and compose the raw equality with the evaluation homology comparison and theta.
The private sectionClass_open_restriction lemma moves section restriction past
these two maps: NatTrans.app_homology gives the evaluation comparison square,
and naturality of sectionCohomologyTheta gives the theta square. Finally compose
with the inverse of I.isoRightDerivedObj at W and use its sheaf naturality to
move restriction past it. Evaluate this morphism equality at y. The equality
transport of sections becomes the identity after substitution. Empty or equal
opens, zero coefficients and p = 0 use the same equations. -/
theorem resolutionSectionClass_open_restriction
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (I : InjectiveResolution F)
    (p : ℕ) (V W : S.Opens) (eWV : W ≤ V)
    (U : X.Opens) (e : U = f ⁻¹ᵁ V) (R : RestrictedResolutionSections I U)
    (R' : RestrictedResolutionSections I (f ⁻¹ᵁ W)) :
    let eU : f ⁻¹ᵁ W ≤ U := by rw [e]; exact f.preimage_mono eWV
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let Q := ((pushforward f).rightDerived p).obj F
    let c := resolutionSectionClass R.resolution K V
      (R.sections ≪≫ eqToIso (congrArg (fun T ↦
        ((RingedSpace.openModuleSections X.toRingedSpace T).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex) e)) p ≫
      Hom.app (I.isoRightDerivedObj (pushforward f) p).inv V
    let c' := resolutionSectionClass R'.resolution K W R'.sections p ≫
      Hom.app (I.isoRightDerivedObj (pushforward f) p).inv W
    ∀ y : (RingedSpace.moduleCohomology U.toScheme.toRingedSpace p).obj
        ((restrictFunctor U.ι).obj F),
      c' (cohomologyOpenRestriction F U (f ⁻¹ᵁ W) eU p y) =
        Q.presheaf.map (homOfLE eWV).op (c y) := by
  subst U
  let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let Q := ((pushforward f).rightDerived p).obj F
  let φ : K.homology p ⟶ Q := (I.isoRightDerivedObj (pushforward f) p).inv
  have hr := restrictedResolution_open_cohomology I (f ⁻¹ᵁ V) (f ⁻¹ᵁ W)
    (f.preimage_mono eWV) R R' p
  have hn := sectionClass_open_restriction K V W eWV p
  dsimp only at hn
  let := RingedSpace.globalSectionsFunctor_additive (f ⁻¹ᵁ V).toScheme.toRingedSpace
  let := RingedSpace.globalSectionsFunctor_additive (f ⁻¹ᵁ W).toScheme.toRingedSpace
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p
  let aV := (forget₂ _ AddCommGrpCat.{u}).map
    (R.resolution.isoRightDerivedObj
      (RingedSpace.globalSectionsFunctor (f ⁻¹ᵁ V).toScheme.toRingedSpace) p).hom ≫
    (((RingedSpace.globalSectionsComplex R.resolution).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{u})).inv ≫ H.map R.sections.hom
  let aW := (forget₂ _ AddCommGrpCat.{u}).map
    (R'.resolution.isoRightDerivedObj
      (RingedSpace.globalSectionsFunctor (f ⁻¹ᵁ W).toScheme.toRingedSpace) p).hom ≫
    (((RingedSpace.globalSectionsComplex R'.resolution).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{u})).inv ≫ H.map R'.sections.hom
  let tV := (((((SheafOfModules.forget S.ringCatSheaf).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K).sc p).mapHomologyIso
      (PresheafOfModules.toPresheaf S.ringCatSheaf.obj ⋙
        (CategoryTheory.evaluation S.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V))).hom ≫
    ((PresheafOfModules.toPresheaf S.ringCatSheaf.obj).map
      (sectionCohomologyTheta K p)).app (op V)
  let tW := (((((SheafOfModules.forget S.ringCatSheaf).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K).sc p).mapHomologyIso
      (PresheafOfModules.toPresheaf S.ringCatSheaf.obj ⋙
        (CategoryTheory.evaluation S.Opensᵒᵖ AddCommGrpCat.{u}).obj (op W))).hom ≫
    ((PresheafOfModules.toPresheaf S.ringCatSheaf.obj).map
      (sectionCohomologyTheta K p)).app (op W)
  let r := (NatTrans.mapHomologicalComplex
    (Functor.whiskerLeft (SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.toPresheaf X.ringCatSheaf.obj)
      ((CategoryTheory.evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).map
        (homOfLE (f.preimage_mono eWV)).op)) (ComplexShape.up ℕ)).app I.cocomplex
  have hrSq : CommSq aV
      (cohomologyOpenRestriction F (f ⁻¹ᵁ V) (f ⁻¹ᵁ W) (f.preimage_mono eWV) p)
      (H.map r) aW := by
    constructor
    simpa only [aV, aW, Category.assoc, cohomologyOpenRestriction] using hr.symm
  have hnSq : CommSq tV (H.map r)
      ((K.homology p).presheaf.map (homOfLE eWV).op) tW := by
    have hrmap : r = (NatTrans.mapHomologicalComplex
        (Functor.whiskerLeft (SheafOfModules.forget S.ringCatSheaf ⋙
          PresheafOfModules.toPresheaf S.ringCatSheaf.obj)
          ((CategoryTheory.evaluation S.Opensᵒᵖ AddCommGrpCat.{u}).map
            (homOfLE eWV).op)) (ComplexShape.up ℕ)).app K := by
      ext n
      rfl
    rewrite [hrmap]
    constructor
    simpa only [tV, tW, Category.assoc] using hn.symm
  have hs : cohomologyOpenRestriction F (f ⁻¹ᵁ V) (f ⁻¹ᵁ W)
      (f.preimage_mono eWV) p ≫ resolutionSectionClass R'.resolution K W R'.sections p =
    resolutionSectionClass R.resolution K V R.sections p ≫
      (K.homology p).presheaf.map (homOfLE eWV).op := by
    simpa only [aV, aW, tV, tW, resolutionSectionClass, Category.assoc] using
      (hrSq.horiz_comp hnSq).w.symm
  have hφ := ((SheafOfModules.forget S.ringCatSheaf ⋙
    PresheafOfModules.toPresheaf S.ringCatSheaf.obj).map φ).naturality
      (homOfLE eWV).op
  change (K.homology p).presheaf.map (homOfLE eWV).op ≫ Hom.app φ W =
    Hom.app φ V ≫ Q.presheaf.map (homOfLE eWV).op at hφ
  have ht := congrArg (fun q ↦ q ≫ Hom.app φ W) hs
  simp only [Category.assoc] at ht
  rewrite [hφ] at ht
  dsimp only
  intro y
  have hy := ConcreteCategory.congr_hom ht y
  simpa only [Iso.trans_hom, eqToIso_refl, Iso.trans_refl, Iso.refl_hom, Category.comp_id,
    AddCommGrpCat.comp_apply] using hy

end AlgebraicGeometry.Scheme.Modules
