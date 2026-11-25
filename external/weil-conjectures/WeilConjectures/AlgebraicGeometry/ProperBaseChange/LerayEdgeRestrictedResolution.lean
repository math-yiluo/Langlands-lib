/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.AlgebraicGeometry.LerayDegenerateSections
import WeilConjectures.AlgebraicGeometry.RestrictedResolutionCohomology
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.LerayWholeOpenClass

/-! # The cocycle Leray edge on a restricted resolution

## References

* Stacks Project, Tag 01E4
* Tag 01F4(2), and Tag 01FB
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives
attribute [local irreducible] moduleCohomologyFMap sectionCohomologyTheta
  resolutionSectionClass

set_option backward.defeqAttrib.useBackward true in
private theorem sectionClass_restriction {Y : Scheme.{u}}
    (L : CochainComplex Y.Modules ℕ) (V : Y.Opens) (p : ℕ) :
    let E := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj
    let A := ((SheafOfModules.forget Y.ringCatSheaf).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj L
    let ev := CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}
    let r := (NatTrans.mapHomologicalComplex
      (Functor.whiskerLeft (SheafOfModules.forget Y.ringCatSheaf ⋙ E)
        (ev.map (homOfLE (show V ≤ ⊤ from le_top)).op))
      (ComplexShape.up ℕ)).app L
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map r ≫
      ((A.sc p).mapHomologyIso (E ⋙ ev.obj (op V))).hom ≫
      (E.map (sectionCohomologyTheta L p)).app (op V) =
    ((A.sc p).mapHomologyIso (E ⋙ ev.obj (op ⊤))).hom ≫
      (E.map (sectionCohomologyTheta L p)).app (op ⊤) ≫
      (L.homology p).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op := by
  dsimp only
  let E := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj
  let A := ((SheafOfModules.forget Y.ringCatSheaf).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj L
  let ev := CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}
  let τ := Functor.whiskerLeft E (ev.map (homOfLE (show V ≤ ⊤ from le_top)).op)
  have ht := NatTrans.app_homology τ (A.sc p)
  have hn := (E.map (sectionCohomologyTheta L p)).naturality
    (homOfLE (show V ≤ ⊤ from le_top)).op
  let r := (NatTrans.mapHomologicalComplex
    (Functor.whiskerLeft (SheafOfModules.forget Y.ringCatSheaf ⋙ E)
      (ev.map (homOfLE (show V ≤ ⊤ from le_top)).op))
    (ComplexShape.up ℕ)).app L
  have hc :
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map r ≫
        ((A.sc p).mapHomologyIso (E ⋙ ev.obj (op V))).hom =
      ((A.sc p).mapHomologyIso (E ⋙ ev.obj (op ⊤))).hom ≫
        (E.obj (A.homology p)).map (homOfLE (show V ≤ ⊤ from le_top)).op := by
    rw [← cancel_epi ((A.sc p).mapHomologyIso (E ⋙ ev.obj (op ⊤))).inv]
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
    (fun t ↦ ((A.sc p).mapHomologyIso (E ⋙ ev.obj (op ⊤))).hom ≫ t) hn

set_option backward.defeqAttrib.useBackward true in
private theorem restrictedResolution_sectionClass {Z Y : Scheme.{u}}
    (h : Z ⟶ Y) {G : Z.Modules} (I : InjectiveResolution G)
    (V : Y.Opens) (U : Z.Opens) (e : U = h ⁻¹ᵁ V)
    (R : RestrictedResolutionSections I U) (p : ℕ) :
    let L := ((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    resolutionSectionClass I L ⊤ (Iso.refl _) p ≫
      (L.homology p).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op =
    moduleCohomologyRestriction U G p ≫
      resolutionSectionClass R.resolution L V
        (R.sections ≪≫ eqToIso (congrArg (fun T ↦
          ((RingedSpace.openModuleSections Z.toRingedSpace T).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex) e)) p := by
  subst U
  let := RingedSpace.globalSectionsFunctor_additive Z.toRingedSpace
  let := RingedSpace.globalSectionsFunctor_additive (h ⁻¹ᵁ V).toScheme.toRingedSpace
  let L := ((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p
  -- Fix the section complexes before composing their homology comparisons.
  let C := ((RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let D := ((RingedSpace.openModuleSections Z.toRingedSpace (h ⁻¹ᵁ V)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj I.cocomplex
  let C' := ((RingedSpace.globalSectionsFunctor (h ⁻¹ᵁ V).toScheme.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      R.resolution.cocomplex
  let a := (forget₂ _ AddCommGrpCat.{u}).map
    (I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor Z.toRingedSpace) p).hom
  let b : _ ⟶ H.obj C := (((RingedSpace.globalSectionsComplex I).sc p).mapHomologyIso
    (forget₂ _ AddCommGrpCat.{u})).inv
  let a' := (forget₂ _ AddCommGrpCat.{u}).map
    (R.resolution.isoRightDerivedObj
      (RingedSpace.globalSectionsFunctor (h ⁻¹ᵁ V).toScheme.toRingedSpace) p).hom
  let b' : _ ⟶ H.obj C' := (((RingedSpace.globalSectionsComplex R.resolution).sc p).mapHomologyIso
    (forget₂ _ AddCommGrpCat.{u})).inv
  let t := fun W : Y.Opens ↦
    (((((SheafOfModules.forget Y.ringCatSheaf).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj L).sc p).mapHomologyIso
        (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙
          (CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op W))).hom ≫
    ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
      (sectionCohomologyTheta L p)).app (op W)
  let t0 : H.obj C ⟶ (L.homology p).presheaf.obj (op ⊤) := t ⊤
  let tV : H.obj D ⟶ (L.homology p).presheaf.obj (op V) := t V
  let rZ : C ⟶ D := (NatTrans.mapHomologicalComplex
    (Functor.whiskerLeft (SheafOfModules.forget Z.ringCatSheaf ⋙
      PresheafOfModules.toPresheaf Z.ringCatSheaf.obj)
      ((CategoryTheory.evaluation Z.Opensᵒᵖ AddCommGrpCat.{u}).map
        (homOfLE (show h ⁻¹ᵁ V ≤ ⊤ from le_top)).op))
    (ComplexShape.up ℕ)).app I.cocomplex
  let rY : C ⟶ D := (NatTrans.mapHomologicalComplex
    (Functor.whiskerLeft (SheafOfModules.forget Y.ringCatSheaf ⋙
      PresheafOfModules.toPresheaf Y.ringCatSheaf.obj)
      ((CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).map
        (homOfLE (show V ≤ ⊤ from le_top)).op))
    (ComplexShape.up ℕ)).app L
  have hrmap : rZ = rY := HomologicalComplex.hom_ext _ _ (fun _ ↦ rfl)
  have hr : moduleCohomologyRestriction (h ⁻¹ᵁ V) G p ≫ a' ≫ b' ≫ H.map R.sections.hom =
      a ≫ b ≫ H.map rY :=
    (restrictedResolution_cohomology I (h ⁻¹ᵁ V) R p).trans
      (congrArg (fun q ↦ a ≫ b ≫ H.map q) hrmap)
  have hn : H.map rY ≫ tV = t0 ≫
      (L.homology p).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op :=
    (sectionClass_restriction L V p).trans (Category.assoc _ _ _).symm
  let r := (L.homology p).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
  have hid : H.map (𝟙 C) ≫ t0 = t0 :=
    (congrArg (fun q ↦ q ≫ t0) (H.map_id C)).trans (Category.id_comp _)
  unfold resolutionSectionClass
  dsimp only
  simp only [Iso.trans_hom, eqToIso_refl, Iso.refl_hom, Category.comp_id]
  change (a ≫ b ≫ H.map (𝟙 C) ≫ t0) ≫ r =
    moduleCohomologyRestriction (h ⁻¹ᵁ V) G p ≫ a' ≫ b' ≫ H.map R.sections.hom ≫ tV
  calc
    (a ≫ b ≫ H.map (𝟙 C) ≫ t0) ≫ r = (a ≫ b ≫ t0) ≫ r :=
      congrArg (fun q ↦ (a ≫ b ≫ q) ≫ r) hid
    _ = a ≫ b ≫ (t0 ≫ r) := by simp only [Category.assoc]
    _ = a ≫ b ≫ H.map rY ≫ tV := congrArg (fun q ↦ a ≫ b ≫ q) hn.symm
    _ = (a ≫ b ≫ H.map rY) ≫ tV := by simp only [Category.assoc]
    _ = (moduleCohomologyRestriction (h ⁻¹ᵁ V) G p ≫ a' ≫ b' ≫
        H.map R.sections.hom) ≫ tV := congrArg (fun q ↦ q ≫ tV) hr.symm
    _ = _ := by simp only [Category.assoc]

/-- Restricting a global class and applying the restricted-resolution class map
computes the restriction of its classical Leray edge. This concerns a single morphism,
with no square, derived pullback, top-degree bound or derived adjunction.
-/
theorem lerayEdge_restrictedResolution {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (I : InjectiveResolution F) (n : ℕ) (V : S.Opens)
    (U : X.Opens) (hU : U = f ⁻¹ᵁ V) (R : RestrictedResolutionSections I U) :
    moduleCohomologyRestriction U F n ≫
      resolutionSectionClass R.resolution
        (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
        V (R.sections ≪≫ eqToIso (congrArg (fun W : X.Opens ↦
          ((RingedSpace.openModuleSections X.toRingedSpace W).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex) hU)) n ≫
      Hom.app (I.isoRightDerivedObj (pushforward f) n).inv V =
    ((Classical.choose (exists_lerayEdge_isIso_of_vanishing f)) n).app F ≫
      ((((pushforward f).rightDerived n).obj F).presheaf.map
        (homOfLE (show V ≤ ⊤ from le_top)).op) := by
  let K : CochainComplex S.Modules ℕ :=
    ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let φ := (I.isoRightDerivedObj (pushforward f) n).inv
  let c := resolutionSectionClass I K ⊤ (Iso.refl _) n
  let r := (((pushforward f).rightDerived n).obj F).presheaf.map
    (homOfLE (show V ≤ ⊤ from le_top)).op
  have hr := restrictedResolution_sectionClass f I V U hU R n
  have hn := (Hom.mapPresheaf φ).naturality (homOfLE (show V ≤ ⊤ from le_top)).op
  change (K.homology n).presheaf.map _ ≫ Hom.app φ V = Hom.app φ ⊤ ≫ r at hn
  calc
    _ = (moduleCohomologyRestriction U F n ≫ _) ≫ Hom.app φ V :=
      (Category.assoc _ _ _).symm
    _ = (c ≫ (K.homology n).presheaf.map _) ≫ Hom.app φ V :=
      congrArg (fun q ↦ q ≫ Hom.app φ V) hr.symm
    _ = c ≫ ((K.homology n).presheaf.map _ ≫ Hom.app φ V) := Category.assoc _ _ _
    _ = c ≫ (Hom.app φ ⊤ ≫ r) := congrArg (fun q ↦ c ≫ q) hn
    _ = (c ≫ Hom.app φ ⊤) ≫ r := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun q ↦ q ≫ r) (whole_open_leray_edge f F I n)

end AlgebraicGeometry.Scheme.Modules
