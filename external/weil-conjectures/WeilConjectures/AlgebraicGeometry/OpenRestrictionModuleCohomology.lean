/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Ext


public import WeilConjectures.Topology.OpenModuleCohomology
import WeilConjectures.AlgebraicGeometry.SchemeModulesEnoughInjectives
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

import WeilConjectures.Topology.RestrictInjectiveResolution
import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Natural comparison of restriction cohomology and open derived sections

Source: Stacks Project, Cohomology, Tags 01E1 and 01E4.
(blueprint: lem-pc-open-restriction-module-cohomology).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Scheme.Modules.enoughInjectives
  comp_preservesFiniteLimits comp_preservesFiniteColimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem openComparison_enoughInjectives (X : RingedSpace.{u}) :
    EnoughInjectives (SheafOfModules.{u} (moduleRings X)) :=
  (RingedSpace.moduleSheaves_abelian_enoughInjectives X).2

attribute [local instance] openComparison_enoughInjectives

noncomputable section

/-- Restrict a resolution to an open subscheme, preserving its actual terms. -/
private def restrictedResolution (X : Scheme.{u}) (U : X.Opens) {M : X.Modules}
    (I : InjectiveResolution M) :
    InjectiveResolution ((Scheme.Modules.restrictFunctor U.ι).obj M) := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let : R.Additive := ⟨by intros; rfl⟩
  let E := (Scheme.Modules.overEquiv U).functor
  let O := SheafOfModules.overFunctor X.ringCatSheaf U
  let eR := Scheme.Modules.overFunctorEquiv U
  have hlim := (open_restriction_adjunction_exact X.toRingedSpace U).1
  have hcolim := (open_restriction_adjunction_exact X.toRingedSpace U).2.1
  let : PreservesFiniteLimits O := hlim
  let : PreservesFiniteColimits O := hcolim
  let : PreservesFiniteLimits R := preservesFiniteLimits_of_natIso eR
  let : PreservesFiniteColimits R := preservesFiniteColimits_of_natIso eR
  have hinj (n : ℕ) : Injective (R.obj (I.cocomplex.X n)) := by
    have h := (RingedSpace.restrict_injectiveResolution X.toRingedSpace U M I).2 n
    exact Injective.of_iso (eR.app (I.cocomplex.X n)) (E.injective_obj_of_injective h)
  let e₀ := (HomologicalComplex.singleMapHomologicalComplex R (.up ℕ) 0).app M
  exact
    { cocomplex := (R.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
      injective := hinj
      ι := e₀.inv ≫ (R.mapHomologicalComplex (.up ℕ)).map I.ι
      quasiIso := by infer_instance }

private theorem restrictedResolution_augmentation (X : Scheme.{u}) (U : X.Opens)
    {M : X.Modules} (I : InjectiveResolution M) :
    (restrictedResolution X U I).ι.f 0 =
      (Scheme.Modules.restrictFunctor U.ι).map (I.ι.f 0) := by
  simp [restrictedResolution]

/-- Restriction identifies global sections on the subscheme with sections on the open. -/
private def openSectionsIso (X : Scheme.{u}) (U : X.Opens) :
    RingedSpace.openModuleSections X.toRingedSpace U ≅
      Scheme.Modules.restrictFunctor U.ι ⋙
        RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace ⋙
          forget₂ (ModuleCat.{u}
            ((moduleRings U.toScheme.toRingedSpace).obj.obj (Opposite.op ⊤)))
              AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun (M : X.Modules) ↦ by
    change Γ(M, U) ≅ Γ(Scheme.Modules.restrict M U.ι, ⊤)
    exact ((Scheme.Modules.toPresheaf X).obj M |>.mapIso (eqToIso (by simp)).op) ≪≫
      (Scheme.Modules.restrictAppIso U.ι M ⊤).symm)
    (by
      intro M N f
      change ((Scheme.Modules.toPresheaf X).map f).app (Opposite.op U) ≫
          ((Scheme.Modules.toPresheaf X).obj N).map
            (eqToHom (by simp : U.ι ''ᵁ ⊤ = U)).op =
        ((Scheme.Modules.toPresheaf X).obj M).map
          (eqToHom (by simp : U.ι ''ᵁ ⊤ = U)).op ≫
            ((Scheme.Modules.toPresheaf X).map f).app (Opposite.op (U.ι ''ᵁ ⊤))
      exact ((Scheme.Modules.toPresheaf X).map f).naturality _ |>.symm)

/-- The section-complex comparison followed by exact scalar forgetting on homology. -/
private def openHomologyIso (X : Scheme.{u}) (U : X.Opens) (p : ℕ) :
    (RingedSpace.openModuleSections X.toRingedSpace U).mapHomologicalComplex (.up ℕ) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) p ≅
      (Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℕ) ⋙
        (RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace).mapHomologicalComplex
          (.up ℕ) ⋙ HomologicalComplex.homologyFunctor _ (.up ℕ) p ⋙
            forget₂ (ModuleCat.{u}
              ((moduleRings U.toScheme.toRingedSpace).obj.obj (Opposite.op ⊤)))
                AddCommGrpCat.{u} := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let : R.Additive := ⟨by intros; rfl⟩
  let S : U.toScheme.Modules ⥤ _ :=
    RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace
  let : S.Additive := ⟨by intros; rfl⟩
  let Q := forget₂ (ModuleCat.{u}
    ((moduleRings U.toScheme.toRingedSpace).obj.obj (Opposite.op ⊤))) AddCommGrpCat.{u}
  let e := Functor.isoWhiskerLeft
    (R.mapHomologicalComplex (.up ℕ) ⋙ S.mapHomologicalComplex (.up ℕ) ⋙
      HomologicalComplex.shortComplexFunctor _ (.up ℕ) p)
    (ShortComplex.homologyFunctorIso Q)
  exact Functor.isoWhiskerRight
    (NatIso.mapHomologicalComplex (openSectionsIso X U) (.up ℕ))
      (HomologicalComplex.homologyFunctor _ (.up ℕ) p) ≪≫ e

private def openResolutionIso (X : Scheme.{u}) (U : X.Opens) (p : ℕ)
    {M : X.Modules} (I : InjectiveResolution M) :
    ((RingedSpace.openModuleSections X.toRingedSpace U).rightDerived p).obj M ≅
      ((Scheme.Modules.restrictFunctor U.ι ⋙
        RingedSpace.moduleCohomology U.toScheme.toRingedSpace p ⋙
          forget₂ (ModuleCat.{u}
            ((moduleRings U.toScheme.toRingedSpace).obj.obj (Opposite.op ⊤)))
              AddCommGrpCat.{u}).obj M) := by
  let T : X.Modules ⥤ AddCommGrpCat.{u} :=
    RingedSpace.openModuleSections X.toRingedSpace U
  let : T.Additive := ⟨by intros; rfl⟩
  let S : U.toScheme.Modules ⥤ _ :=
    RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace
  let : S.Additive := ⟨by intros; rfl⟩
  exact
    I.isoRightDerivedObj (RingedSpace.openModuleSections X.toRingedSpace U) p ≪≫
      (openHomologyIso X U p).app I.cocomplex ≪≫
        (forget₂ _ AddCommGrpCat.{u}).mapIso
        ((restrictedResolution X U I).isoRightDerivedObj
          (RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace) p).symm

private theorem openResolutionIso_naturality (X : Scheme.{u}) (U : X.Opens) (p : ℕ)
    {M N : X.Modules} (a : M ⟶ N) (I : InjectiveResolution M) (J : InjectiveResolution N)
    (g : I.cocomplex ⟶ J.cocomplex)
    (hg : I.ι.f 0 ≫ g.f 0 = a ≫ J.ι.f 0) :
    ((RingedSpace.openModuleSections X.toRingedSpace U).rightDerived p).map a ≫
        (openResolutionIso X U p J).hom =
      (openResolutionIso X U p I).hom ≫
        (Scheme.Modules.restrictFunctor U.ι ⋙
          RingedSpace.moduleCohomology U.toScheme.toRingedSpace p ⋙
            forget₂ (ModuleCat.{u}
              ((moduleRings U.toScheme.toRingedSpace).obj.obj (Opposite.op ⊤)))
                AddCommGrpCat.{u}).map a := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let : R.Additive := ⟨by intros; rfl⟩
  let S : U.toScheme.Modules ⥤ _ :=
    RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace
  let : S.Additive := ⟨by intros; rfl⟩
  let Q := forget₂ (ModuleCat.{u}
    ((moduleRings U.toScheme.toRingedSpace).obj.obj (Opposite.op ⊤))) AddCommGrpCat.{u}
  let T : X.Modules ⥤ AddCommGrpCat.{u} :=
    RingedSpace.openModuleSections X.toRingedSpace U
  let : T.Additive := ⟨by intros; rfl⟩
  let gR : (restrictedResolution X U I).cocomplex ⟶
      (restrictedResolution X U J).cocomplex :=
    (R.mapHomologicalComplex (.up ℕ)).map g
  have hgR : (restrictedResolution X U I).ι.f 0 ≫ gR.f 0 =
      R.map a ≫ (restrictedResolution X U J).ι.f 0 := by
    rw [restrictedResolution_augmentation, restrictedResolution_augmentation]
    exact (R.map_comp _ _).symm.trans ((congrArg R.map hg).trans (R.map_comp _ _))
  have hT := I.isoRightDerivedObj_hom_naturality a J g hg T p
  have hS := congrArg Q.map
    ((restrictedResolution X U I).isoRightDerivedObj_inv_naturality
      (R.map a) (restrictedResolution X U J) gR hgR S p)
  simp only [Functor.map_comp] at hS
  have hH := (openHomologyIso X U p).hom.naturality g
  dsimp only [openResolutionIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [Category.assoc]
  simp only [Functor.comp_map] at hH
  erw [reassoc_of% hT, reassoc_of% hH]
  simp only [R, S, Q, gR, Functor.comp_map, RingedSpace.moduleCohomology] at hS ⊢
  erw [← hS]
  rfl

private def openDerivedIso (X : Scheme.{u}) (U : X.Opens) (p : ℕ) :
    (RingedSpace.openModuleSections X.toRingedSpace U).rightDerived p ≅
      Scheme.Modules.restrictFunctor U.ι ⋙
        RingedSpace.moduleCohomology U.toScheme.toRingedSpace p ⋙
          forget₂ (ModuleCat.{u}
            ((moduleRings U.toScheme.toRingedSpace).obj.obj (Opposite.op ⊤)))
              AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun M ↦ openResolutionIso X U p (injectiveResolution M))
    (fun a ↦ openResolutionIso_naturality X U p a _ _
      (InjectiveResolution.desc a _ _) (InjectiveResolution.desc_commutes_zero a _ _))

/-- Open restriction commutes with derived module sections, after forgetting scalars.

Source: Stacks Project, Cohomology, Lemma 20.7.1, Tag 01E1.
(blueprint: lem-pc-open-restriction-module-cohomology).

Proof: Write R for restriction along U.ι. Open restriction is exact and its exact
left adjoint is extension by zero, hence R preserves injectives. Transport the
restricted resolution through Modules.overEquiv U, with overFunctorEquiv identifying
it with R applied termwise to the original resolution. The restrictAppIso at the
terminal open identifies its global sections complex with sections on U. Forgetting
scalars is exact, so its mapHomologyIso identifies the two homology objects. Conjugate
this comparison by isoRightDerivedObj for the original and restricted resolutions.
For a coefficient map choose a lift to the original resolutions and restrict it.
Naturality of restrictAppIso, mapHomologyIso and isoRightDerivedObj proves naturality
of the conjugated comparison. Applying the same computation to an identity lift
shows independence of the resolution. All comparison arrows are isomorphisms, so
these components give a natural isomorphism. Empty U and degree zero are included:
restriction, evaluation and scalar forgetting use the same definitions there. -/
theorem nonempty_openRestriction_moduleCohomology_iso
    (X : Scheme.{u}) (U : X.Opens) (p : ℕ) :
    Nonempty ((Scheme.Modules.restrictFunctor U.ι ⋙
      RingedSpace.moduleCohomology U.toScheme.toRingedSpace p ⋙
        forget₂ (ModuleCat.{u}
          ((moduleRings U.toScheme.toRingedSpace).obj.obj (Opposite.op ⊤)))
            AddCommGrpCat.{u}) ≅
      RingedSpace.openModuleCohomology X.toRingedSpace p U) := by
  exact ⟨(openDerivedIso X U p).symm⟩

end

end AlgebraicGeometry
