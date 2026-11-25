/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeResolutionOpenMap
import WeilConjectures.AlgebraicGeometry.FlatPullbackResolutionRawMateSections

/-! # The open cohomology map of a fixed resolution lift

Source: Stacks Project, Cohomology, Tags 01FB and 01E4.
-/

@[expose] public section
universe uBC
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives
attribute [local irreducible] tensorPullback tensorPullbackObj tensorPullbackMap


private def rawSectionClass {Y : Scheme.{uBC}}
    (K : CochainComplex Y.Modules ℕ) (V : Y.Opens) (p : ℕ) :
    (((RingedSpace.openModuleSections Y.toRingedSpace V).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).homology p ⟶ (K.homology p).presheaf.obj (op V) :=
  let U := SheafOfModules.forget Y.ringCatSheaf
  let E := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙
    (CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{uBC}).obj (op V)
  ((((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc p).mapHomologyIso E).hom ≫
    E.map (sectionCohomologyTheta K p)

private theorem resolutionSectionClass_eq {Z Y : Scheme.{uBC}} {G : Z.Modules}
    (R : InjectiveResolution G) (K : CochainComplex Y.Modules ℕ) (V : Y.Opens)
    (a : ((RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{uBC}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        R.cocomplex ≅
      ((RingedSpace.openModuleSections Y.toRingedSpace V).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K) (p : ℕ) :
    letI := RingedSpace.globalSectionsFunctor_additive Z.toRingedSpace
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{uBC} (ComplexShape.up ℕ) p
    resolutionSectionClass R K V a p =
      ((forget₂ _ AddCommGrpCat.{uBC}).mapIso
        (R.isoRightDerivedObj (RingedSpace.globalSectionsFunctor Z.toRingedSpace) p) ≪≫
        (((RingedSpace.globalSectionsComplex R).sc p).mapHomologyIso
          (forget₂ _ AddCommGrpCat.{uBC})).symm ≪≫ H.mapIso a).hom ≫
        rawSectionClass K V p := by
  dsimp only
  simp only [resolutionSectionClass, rawSectionClass, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  ext x
  rfl

attribute [local irreducible] sectionCohomologyTheta flatBaseChangeResolutionBeta
attribute [local irreducible] flatBaseChangeResolutionOpenMap
attribute [local irreducible] FlatBaseChangeOpenChoices.sourceClass
attribute [local irreducible] FlatBaseChangeOpenChoices.targetClass

private theorem adjoint_transport
    {C D : Type*} [Category* C] [Category* D]
    (A : C ⥤ D) (B : D ⥤ C) (adj : A ⊣ B)
    {X X' : C} {Y Y' : D} (eX : X ≅ X') (eY : Y ≅ Y')
    (b : A.obj X' ⟶ Y') :
    adj.homEquiv X Y (A.map eX.hom ≫ b ≫ eY.inv) =
      eX.hom ≫ adj.homEquiv X' Y' b ≫ B.map eY.inv := by
  rw [← Category.assoc, adj.homEquiv_naturality_right,
    adj.homEquiv_naturality_left, Category.assoc]

set_option maxHeartbeats 160000 in
-- Resolution and section comparisons require comparing the composite functor interfaces.
/-- The homology mate of q acts on resolution classes through its open cohomology map.
Source: Stacks Project, Cohomology, Tags 02N7 and 01E4.
(blueprint: lem-weil-pbc-flat-pullback-homology-sections).

Proof: Represent the source section-complex homology class by a cycle s. The unit
followed by pushforward of the termwise adjoint c of q equals q, so it sends s to
q(s). Exactness of tensor pullback identifies the homology comparison in beta with
this cycle-class calculation. The sheafification unit theta is natural for this
calculation, giving equality of the associated cohomology-sheaf sections. In the
open map the inverse target resolution/section isomorphism converts H(q)(s) into
a target cohomology class. Applying targetClass cancels that inverse and applies
theta, followed by the inverse target derived-image comparison. The inverse source
derived-image comparison in sourceClass likewise cancels the source comparison
in beta by adjunction naturality. These cancellations give the displayed formula.
This argument does not use the augmentation of t or a comparison with an h-map. -/
theorem flatBaseChangeResolutionBeta_openMap_sections {X S S' : Scheme.{uBC}}
    (f : X ⟶ S) (g : S' ⟶ S)
    [Flat g] [Flat (pullback.snd g f)] {F : X.Modules}
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex)
    (p : ℕ) :
    ∀ (V : S.Opens)
        (D : FlatBaseChangeOpenChoices f g F I J V)
        (xi : (forget₂ _ AddCommGrpCat.{uBC}).obj
          ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
            ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F))),
        Hom.app ((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv _ _
          (flatBaseChangeResolutionBeta f g I J t p)) V
          (D.sourceClass p xi) =
        D.targetClass p
          (flatBaseChangeResolutionOpenMap f g I J t p V D xi) := by
  intro V D xi
  let := RingedSpace.globalSectionsFunctor_additive (f ⁻¹ᵁ V).toScheme.toRingedSpace
  let := RingedSpace.globalSectionsFunctor_additive
    ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme.toRingedSpace
  let K : CochainComplex S.Modules ℕ :=
    ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let L : CochainComplex S'.Modules ℕ := ((pushforward (pullback.fst g f)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj J.cocomplex
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{uBC} (ComplexShape.up ℕ) p
  let adj : tensorPullback g ⊣ pushforward g := Classical.choose (exists_tensorPullbackAdjunction g)
  let rS := (forget₂ _ AddCommGrpCat.{uBC}).mapIso
    (D.source.resolution.isoRightDerivedObj
      (RingedSpace.globalSectionsFunctor (f ⁻¹ᵁ V).toScheme.toRingedSpace) p) ≪≫
    (((RingedSpace.globalSectionsComplex D.source.resolution).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{uBC})).symm ≪≫ H.mapIso D.source.sections
  let aT := D.target.sections ≪≫
    eqToIso (congrArg (fun U ↦ ((RingedSpace.openModuleSections
      (Limits.pullback g f).toRingedSpace U).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex) (flatBaseChangeOpenEquality f g V))
  let rT := (forget₂ _ AddCommGrpCat.{uBC}).mapIso
    (D.target.resolution.isoRightDerivedObj (RingedSpace.globalSectionsFunctor
      ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme.toRingedSpace) p) ≪≫
    (((RingedSpace.globalSectionsComplex D.target.resolution).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{uBC})).symm ≪≫ H.mapIso aT
  let eS := I.isoRightDerivedObj (pushforward f) p
  let eT := J.isoRightDerivedObj (pushforward (pullback.fst g f)) p
  let b := ((K.sc p).mapHomologyIso (tensorPullback g)).inv ≫
    HomologicalComplex.homologyMap (flatBaseChangeResolutionC f g I J t) p
  have hm := flatBaseChangeResolution_rawMate_sections f g I J t p V
  have hb : adj.homEquiv _ _ (flatBaseChangeResolutionBeta f g I J t p) =
      eS.hom ≫ adj.homEquiv _ _ b ≫ (pushforward g).map eT.inv := by
    simpa only [flatBaseChangeResolutionBeta, eS, eT, b, K, L, adj,
      Category.assoc, HomologicalComplex.homologyFunctor] using
      adjoint_transport (tensorPullback g) (pushforward g) adj eS eT b
  dsimp only [HomologicalComplex.homologyFunctor] at hb
  have hs : D.sourceClass p =
      rS.hom ≫ rawSectionClass K V p ≫ Hom.app eS.inv V := by
    simp only [FlatBaseChangeOpenChoices.sourceClass, resolutionSectionClass_eq,
      Category.assoc]
    rfl
  have ht : D.targetClass p =
      rT.hom ≫ rawSectionClass L (g ⁻¹ᵁ V) p ≫ Hom.app eT.inv (g ⁻¹ᵁ V) := by
    simp only [FlatBaseChangeOpenChoices.targetClass, resolutionSectionClass_eq,
      Category.assoc]
    rfl
  change rawSectionClass K V p ≫ Hom.app (adj.homEquiv _ _ b) V = _ at hm
  have he : D.sourceClass p ≫
      Hom.app (adj.homEquiv _ _ (flatBaseChangeResolutionBeta f g I J t p)) V =
      flatBaseChangeResolutionOpenMap f g I J t p V D ≫ D.targetClass p := by
    simp only [hs, ht, hb]
    simp only [Hom.comp_app, pushforward_map_app, Category.assoc]
    dsimp only [HomologicalComplex.homologyFunctor]
    have hcancel := congrArg (fun a ↦ Hom.app a V) eS.inv_hom_id
    simp only [Hom.comp_app, Hom.id_app, HomologicalComplex.homologyFunctor] at hcancel
    conv_lhs =>
      arg 2
      arg 2
      rw [← Category.assoc, hcancel]
      erw [Category.id_comp]
    conv_lhs =>
      arg 2
      rw [← Category.assoc]
      erw [hm]
    simp only [flatBaseChangeResolutionOpenMap]
    change _ = (rS.hom ≫ _ ≫ rT.inv) ≫
      (rT.hom ≫ rawSectionClass L (g ⁻¹ᵁ V) p ≫ Hom.app eT.inv (g ⁻¹ᵁ V))
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  exact ConcreteCategory.congr_hom he xi

end AlgebraicGeometry.Scheme.Modules
