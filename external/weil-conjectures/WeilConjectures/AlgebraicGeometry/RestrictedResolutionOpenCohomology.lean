/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyAugmentedLift
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Restriction on the homology of fixed-resolution section complexes

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

/-- Transport a commutative square through a functor and two comparison isomorphisms. -/
private theorem map_conjugation_comp
    {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D)
    {A B B' E F : C} {X Y : D} (s : X ≅ H.obj A) (s' : Y ≅ H.obj B)
    (f : X ⟶ Y) (b : A ⟶ B') (a : B ≅ B')
    (v : B ⟶ E) (u : A ⟶ F) (r : F ⟶ E)
    (hf : s.hom ≫ H.map b ≫ H.map a.inv ≫ s'.inv = f)
    (hc : b ≫ a.inv ≫ v = u ≫ r) :
    f ≫ s'.hom ≫ H.map v = s.hom ≫ H.map u ≫ H.map r := by
  rw [← hf]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← H.map_comp, ← H.map_comp, hc, H.map_comp]

/-- A natural comparison transports an augmentation through a target isomorphism. -/
private theorem map_comparison_augmentation
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {S : C ⥤ D} {T : C ⥤ E} (Q : D ⥤ E) (c : S ⋙ Q ⟶ T)
    {F X : C} {A : D} {B : E} (a : F ⟶ X)
    (i : S.obj F ⟶ A) (i' : T.obj F ⟶ B)
    (v : A ⟶ S.obj X) (w : B ≅ T.obj X)
    (h : i ≫ v = S.map a) (h' : i' ≫ w.hom = T.map a) :
    Q.map i ≫ Q.map v ≫ c.app X ≫ w.inv = c.app F ≫ i' := by
  rw [← Category.assoc, ← Q.map_comp, h]
  have hn : Q.map (S.map a) ≫ c.app X = c.app F ≫ T.map a := c.naturality a
  rw [← Category.assoc, hn, Category.assoc, ← h', Category.assoc,
    w.hom_inv_id, Category.comp_id]

/-- Naturality of an adjunction unit transports an augmentation square. -/
private theorem adjunction_unit_map_augmentation
    {C D : Type*} [Category* C] [Category* D]
    {Q : C ⥤ D} {P : D ⥤ C} (adj : Q ⊣ P)
    {F A : C} {F' B : D} (i : F ⟶ A) (i' : F' ⟶ B)
    (t : Q.obj A ⟶ B) (c : Q.obj F ⟶ F')
    (ht : Q.map i ≫ t = c ≫ i') :
    i ≫ adj.unit.app A ≫ P.map t = (adj.unit.app F ≫ P.map c) ≫ P.map i' := by
  have hn : i ≫ adj.unit.app A = adj.unit.app F ≫ P.map (Q.map i) :=
    adj.unit.naturality i
  rw [← Category.assoc, hn, Category.assoc, ← P.map_comp, ht, P.map_comp, Category.assoc]

/-- Pushforward identifies the global-section complexes, with the inverse given by
restriction along the inverse image of the top open. -/
private theorem exists_pushforward_sections_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex X.Modules ℕ) :
    ∃ a : ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj K ≅
      ((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj K),
      ∀ n : ℕ, a.inv.f n = (K.X n).presheaf.map
        (eqToHom (by simp) : (⊤ : X.Opens) ⟶ f ⁻¹ᵁ (⊤ : Y.Opens)).op := by
  let a : ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj K ≅
      ((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj K) := by
    refine (HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ (presheaf (K.X n)).mapIso
        (eqToIso (by simp) : op (f ⁻¹ᵁ (⊤ : Y.Opens)) ≅ op (⊤ : X.Opens))) ?_).symm
    intro n m _
    exact ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
      (K.d n m)).naturality _
  exact ⟨a, fun _ ↦ rfl⟩

/-- The restriction-unit calculation on a single module, independent of resolutions. -/
private theorem restrictedResolution_open_sections_component {Z : Scheme.{u}}
    (U L : Z.Opens) (e : L ≤ U) (K : Z.Modules)
    {D : U.toScheme.Modules} {D' : L.toScheme.Modules}
    (v : D ⟶ (restrictFunctor U.ι).obj K)
    (v' : D' ≅ (restrictFunctor L.ι).obj K) :
    let j := Z.homOfLE e
    let c := (restrictFunctorComp j U.ι).symm ≪≫
      restrictFunctorCongr (Z.homOfLE_ι e)
    Hom.app ((restrictAdjunction j).unit.app D) ⊤ ≫
      Hom.app ((restrictFunctor j).map v ≫ c.hom.app K ≫ v'.inv)
        (j ⁻¹ᵁ (⊤ : U.toScheme.Opens)) ≫
      D'.presheaf.map (eqToHom (by simp) : (⊤ : L.toScheme.Opens) ⟶
        j ⁻¹ᵁ (⊤ : U.toScheme.Opens)).op ≫
      Hom.app v'.hom ⊤ ≫ (restrictAppIso L.ι K ⊤).hom ≫
      K.presheaf.map (eqToHom L.ι_image_top.symm).op =
    Hom.app v ⊤ ≫ (restrictAppIso U.ι K ⊤).hom ≫
      K.presheaf.map (eqToHom U.ι_image_top.symm).op ≫
      K.presheaf.map (homOfLE e).op := by
  intro j c
  simp only [Hom.comp_app, Category.assoc]
  have hn := (Hom.mapPresheaf v'.inv).naturality
    (eqToHom (by simp) : (⊤ : L.toScheme.Opens) ⟶
      j ⁻¹ᵁ (⊤ : U.toScheme.Opens)).op
  change ((restrictFunctor L.ι).obj K).presheaf.map _ ≫ Hom.app v'.inv ⊤ =
    Hom.app v'.inv (j ⁻¹ᵁ (⊤ : U.toScheme.Opens)) ≫
    D'.presheaf.map _ at hn
  rw [← Category.assoc (Hom.app v'.inv _) (D'.presheaf.map _)]
  erw [← hn]
  simp only [Category.assoc]
  have hcan : Hom.app v'.inv ⊤ ≫ Hom.app v'.hom ⊤ = 𝟙 _ := by
    rw [← Hom.comp_app, v'.inv_hom_id, Hom.id_app]
  rw [← Category.assoc (Hom.app v'.inv ⊤)
    (Hom.app v'.hom ⊤), hcan, Category.id_comp]
  have hu := congrArg (fun f ↦ Hom.app f ⊤)
    ((restrictAdjunction j).unit.naturality v)
  change Hom.app v ⊤ ≫
    Hom.app ((restrictAdjunction j).unit.app
      ((restrictFunctor U.ι).obj K)) ⊤ =
    Hom.app ((restrictAdjunction j).unit.app D) ⊤ ≫
    Hom.app ((restrictFunctor j).map v) (j ⁻¹ᵁ (⊤ : U.toScheme.Opens)) at hu
  rw [← Category.assoc (Hom.app ((restrictAdjunction j).unit.app D) ⊤)
    (Hom.app ((restrictFunctor j).map v) _), ← hu]
  simp only [Category.assoc]
  simp only [c, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Hom.comp_app, restrictFunctorComp_inv_app_app, restrictFunctorCongr_hom_app_app,
    restrictAdjunction_unit_app_app, restrictAppIso, Iso.refl_hom]
  erw [Category.id_comp, Category.id_comp]
  simp only [restrict_map, ← Functor.map_comp]
  congr 1

set_option backward.defeqAttrib.useBackward true in
/-- Restriction between arbitrary opens on the homology of a fixed resolution's
section complexes, before the map to a cohomology sheaf.
Source: Stacks Project, Equation 20.7.1.1 (Tag 01E2), Remark 20.14.2 (Tag 01FB).
(blueprint: new-restricted-resolution-open-cohomology)

Proof: Put j = homOfLE e. Restrict R.comparison along j, compose with the
canonical restriction-composition isomorphism, and then R'.comparison inverse.
This gives a map t from j^*R.resolution to R'.resolution. Let beta be the
restriction unit on R.resolution followed by j_*(t). Naturality of the unit,
the restriction-composition isomorphism, and the two augmentation equations
show that beta lifts the coefficient map displayed below.
Construct the canonical global-section comparison a: its inverse components
restrict along j inverse image of top = top. Apply the existing augmented-lift
formula to compute moduleCohomologyFMap from beta and a.
Degreewise, use the pinned components of R.sections and R'.sections. Move the
inverse target comparison past restriction by presheaf naturality and cancel it
with its comparison. Move the source comparison past the unit by naturality.
The restriction-unit and restriction-composition component formulas identify
all remaining maps with maps of I's presheaf of sections. Presheaf functoriality
then gives R.sections followed by restriction of I's sections from U to L.
Apply homology to this chain-map equality and cancel the target resolution
isomorphism to obtain the asserted identity. Empty or equal opens, zero
coefficients, and degree zero use the same equations; no restriction is inverted. -/
theorem restrictedResolution_open_cohomology {Z : Scheme.{u}} {F : Z.Modules}
    (I : InjectiveResolution F) (U L : Z.Opens) (e : L ≤ U)
    (R : RestrictedResolutionSections I U) (R' : RestrictedResolutionSections I L)
    (p : ℕ) :
    let := RingedSpace.globalSectionsFunctor_additive Z.toRingedSpace
    let := RingedSpace.globalSectionsFunctor_additive U.toScheme.toRingedSpace
    let := RingedSpace.globalSectionsFunctor_additive L.toScheme.toRingedSpace
    let j := Z.homOfLE e
    let c := (restrictFunctorComp j U.ι).symm.app F ≪≫
      (restrictFunctorCongr (Z.homOfLE_ι e)).app F
    moduleCohomologyFMap j
      ((restrictAdjunction j).unit.app ((restrictFunctor U.ι).obj F) ≫
        (pushforward j).map c.hom) p ≫
      (forget₂ _ AddCommGrpCat.{u}).map
        (R'.resolution.isoRightDerivedObj
          (RingedSpace.globalSectionsFunctor L.toScheme.toRingedSpace) p).hom ≫
      (((RingedSpace.globalSectionsComplex R'.resolution).sc p).mapHomologyIso
        (forget₂ _ AddCommGrpCat.{u})).inv ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
        R'.sections.hom =
    (forget₂ _ AddCommGrpCat.{u}).map
      (R.resolution.isoRightDerivedObj
        (RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace) p).hom ≫
      (((RingedSpace.globalSectionsComplex R.resolution).sc p).mapHomologyIso
        (forget₂ _ AddCommGrpCat.{u})).inv ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
      R.sections.hom ≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
        ((NatTrans.mapHomologicalComplex
          (Functor.whiskerLeft (SheafOfModules.forget Z.ringCatSheaf ⋙
            PresheafOfModules.toPresheaf Z.ringCatSheaf.obj)
              ((evaluation Z.Opensᵒᵖ AddCommGrpCat.{u}).map
                (homOfLE e).op))
          (ComplexShape.up ℕ)).app I.cocomplex) := by
  let := RingedSpace.globalSectionsFunctor_additive Z.toRingedSpace
  let := RingedSpace.globalSectionsFunctor_additive U.toScheme.toRingedSpace
  let := RingedSpace.globalSectionsFunctor_additive L.toScheme.toRingedSpace
  let j := Z.homOfLE e
  let P := pushforward j
  let Q := restrictFunctor j
  have : Q.Additive := (restrictAdjunction j).left_adjoint_additive
  let c : restrictFunctor U.ι ⋙ Q ≅ restrictFunctor L.ι :=
    (restrictFunctorComp j U.ι).symm ≪≫ restrictFunctorCongr (Z.homOfLE_ι e)
  let t : (Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.resolution.cocomplex ⟶
      R'.resolution.cocomplex :=
    (Q.mapHomologicalComplex (ComplexShape.up ℕ)).map R.comparison.hom ≫
      (NatTrans.mapHomologicalComplex c.hom (ComplexShape.up ℕ)).app I.cocomplex ≫
        R'.comparison.inv
  let β : R.resolution.cocomplex ⟶
      (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj R'.resolution.cocomplex :=
    ((restrictAdjunction j).mapHomologicalComplex (ComplexShape.up ℕ)).unit.app
      R.resolution.cocomplex ≫
      (P.mapHomologicalComplex (ComplexShape.up ℕ)).map t
  let φ : (restrictFunctor U.ι).obj F ⟶ P.obj ((restrictFunctor L.ι).obj F) :=
    (restrictAdjunction j).unit.app ((restrictFunctor U.ι).obj F) ≫ P.map (c.hom.app F)
  have ht := map_comparison_augmentation Q c.hom (I.ι.f 0)
    (R.resolution.ι.f 0) (R'.resolution.ι.f 0) (R.comparison.hom.f 0)
    ((HomologicalComplex.eval _ _ 0).mapIso R'.comparison) R.augmentation R'.augmentation
  have hβ := adjunction_unit_map_augmentation (restrictAdjunction j)
    (R.resolution.ι.f 0) (R'.resolution.ι.f 0) (t.f 0) (c.hom.app F) ht
  let Γ := RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{u}
  obtain ⟨a, ha⟩ := exists_pushforward_sections_iso j R'.resolution.cocomplex
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p
  let r := (NatTrans.mapHomologicalComplex
    (Functor.whiskerLeft (SheafOfModules.forget Z.ringCatSheaf ⋙
      PresheafOfModules.toPresheaf Z.ringCatSheaf.obj)
      ((evaluation Z.Opensᵒᵖ AddCommGrpCat.{u}).map (homOfLE e).op))
    (ComplexShape.up ℕ)).app I.cocomplex
  have hc : (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map β ≫
      a.inv ≫ R'.sections.hom = R.sections.hom ≫ r := by
    apply HomologicalComplex.hom_ext
    intro n
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      HomologicalComplex.comp_f, R'.components, R.components]
    rw [ha]
    exact restrictedResolution_open_sections_component U L e (I.cocomplex.X n)
      (R.comparison.hom.f n) ((HomologicalComplex.eval _ _ n).mapIso R'.comparison)
  let iR := (forget₂ _ AddCommGrpCat.{u}).mapIso
    (R.resolution.isoRightDerivedObj
      (RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace) p) ≪≫
      (((RingedSpace.globalSectionsComplex R.resolution).sc p).mapHomologyIso
        (forget₂ _ AddCommGrpCat.{u})).symm
  let iR' := (forget₂ _ AddCommGrpCat.{u}).mapIso
    (R'.resolution.isoRightDerivedObj
      (RingedSpace.globalSectionsFunctor L.toScheme.toRingedSpace) p) ≪≫
      (((RingedSpace.globalSectionsComplex R'.resolution).sc p).mapHomologyIso
        (forget₂ _ AddCommGrpCat.{u})).symm
  have hmap := moduleCohomologyFMap_of_augmentedLift j φ R'.resolution R.resolution
    β hβ a ha p
  have hfinal := map_conjugation_comp H
    (A := (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.resolution.cocomplex)
    (B := ((RingedSpace.globalSectionsFunctor L.toScheme.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        R'.resolution.cocomplex)
    iR iR' (moduleCohomologyFMap j φ p)
    ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map β) a
    R'.sections.hom R.sections.hom r hmap hc
  simpa only [iR, iR', H, r, φ, P, c, j, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, NatTrans.comp_app, Functor.mapIso_hom, Category.assoc] using hfinal


end AlgebraicGeometry.Scheme.Modules
