/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.Topology.RestrictInjectiveResolution
import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Untwisted comparison with raw section cohomology

Source: Stacks Project, Tags 01E1 and 01E4.
(blueprint: lem-pc-section-cohomology-untwisted-comparisons).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] enoughInjectives


private noncomputable def rawRestrictionResolution (X : Scheme.{u}) (U : X.Opens)
    {M : X.Modules} (I : InjectiveResolution M) :
    InjectiveResolution ((restrictFunctor U.ι).obj M) := by
  let R := restrictFunctor U.ι
  let : R.Additive := ⟨by intros; rfl⟩
  let E := (overEquiv U).functor
  let O := SheafOfModules.overFunctor X.ringCatSheaf U
  let eR := overFunctorEquiv U
  have hlim := (open_restriction_adjunction_exact X.toRingedSpace U).1
  have hcolim := (open_restriction_adjunction_exact X.toRingedSpace U).2.1
  let : CategoryTheory.Limits.PreservesFiniteLimits O := hlim
  let : CategoryTheory.Limits.PreservesFiniteColimits O := hcolim
  let : CategoryTheory.Limits.PreservesFiniteLimits R :=
    CategoryTheory.Limits.preservesFiniteLimits_of_natIso eR
  let : CategoryTheory.Limits.PreservesFiniteColimits R :=
    CategoryTheory.Limits.preservesFiniteColimits_of_natIso eR
  have hinj (n : ℕ) : Injective (R.obj (I.cocomplex.X n)) := by
    have h := (RingedSpace.restrict_injectiveResolution X.toRingedSpace U M I).2 n
    exact Injective.of_iso (eR.app (I.cocomplex.X n)) (E.injective_obj_of_injective h)
  let e₀ := (HomologicalComplex.singleMapHomologicalComplex R (.up ℕ) 0).app M
  exact
    { cocomplex := (R.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
      injective := hinj
      ι := e₀.inv ≫ (R.mapHomologicalComplex (.up ℕ)).map I.ι
      quasiIso := by infer_instance }

private noncomputable def restrictOpenSectionsIso (X : Scheme.{u}) (W : X.Opens)
    (V : W.toScheme.Opens) :
    restrictFunctor W.ι ⋙ RingedSpace.openModuleSections W.toScheme.toRingedSpace V ≅
      RingedSpace.openModuleSections X.toRingedSpace (W.ι ''ᵁ V) :=
  NatIso.ofComponents (fun M ↦ restrictAppIso W.ι M V)
    (by
      intro M N g
      ext z
      rfl)

private noncomputable def scalarHom {Y : Scheme.{u}} (G : Y.Modules)
    (b : Γ(Y, ⊤)) : G ⟶ G :=
  (ρ_ G).inv ≫ G ◁ homOfGlobalSection (𝟙_ Y.Modules) (unitSectionsEquiv ⊤ b) ≫ (ρ_ G).hom

private theorem scalarHom_app {Y : Scheme.{u}} (G : Y.Modules)
    (b : Γ(Y, ⊤)) (U : Y.Opens) (z : Γ(G, U)) :
    (scalarHom G b).app U z = (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom b • z := by
  simp only [scalarHom, Hom.comp_app, ConcreteCategory.comp_apply]
  rw [rightUnitor_inv_app, whiskerLeft_app_tmulSection]
  change (ρ_ G).hom.app U (tmulSection z
    ((homOfGlobalSection (𝟙_ Y.Modules) (unitSectionsEquiv ⊤ b)).app U
      (1 : Γ(Y, U)))) = _
  rw [homOfGlobalSection_app_one, presheaf_map_unitSectionsEquiv,
    rightUnitor_hom_app_tmulSection]

private theorem scalarHom_naturality {Y : Scheme.{u}} {G H : Y.Modules}
    (g : G ⟶ H) (b : Γ(Y, ⊤)) :
    g ≫ scalarHom H b = scalarHom G b ≫ g := by
  apply hom_ext
  intro U
  ext z
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, scalarHom_app, Hom.app_smul]

private noncomputable def sectionsCongr (X : Scheme.{u}) {U V : X.Opens} (h : U = V) :
    RingedSpace.openModuleSections X.toRingedSpace U ≅
      RingedSpace.openModuleSections X.toRingedSpace V :=
  NatIso.ofComponents (fun (M : X.Modules) ↦ M.presheaf.mapIso (eqToIso h.symm).op)
    (by
      intro M N g
      exact (((toPresheaf X).map g).naturality _).symm)

private theorem scalar_homology_transport
    {C : Type*} [Category C] [Abelian C]
    (A : ShortComplex AddCommGrpCat.{u}) (B : ShortComplex C)
    (E : C ⥤ AddCommGrpCat.{u}) [E.PreservesZeroMorphisms] [E.PreservesHomology]
    (φ : A ⟶ A) (e : A ⟶ B.map E) (τ : E ⟶ E)
    (h : φ ≫ e = e ≫ B.mapNatTrans τ) :
    ShortComplex.homologyMap φ ≫ ShortComplex.homologyMap e ≫
        (B.mapHomologyIso E).hom =
      ShortComplex.homologyMap e ≫ (B.mapHomologyIso E).hom ≫ τ.app B.homology := by
  have hm := congrArg (fun g ↦ ShortComplex.homologyMap g) h
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp,
    ShortComplex.homologyMap_mapNatTrans] at hm
  have hm' := congrArg (fun g ↦ g ≫ (B.mapHomologyIso E).hom) hm
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hm'

private theorem pullback_scalar_restrict {X T : Scheme.{u}}
    (f : X ⟶ T) (W V : T.Opens) (hV : V ≤ W)
    (U : (f ⁻¹ᵁ W).toScheme.Opens) (h : (f ⁻¹ᵁ W).ι ''ᵁ U = f ⁻¹ᵁ V)
    (r : Γ(T, W)) :
    (X.presheaf.map (eqToHom h.symm).op).hom
      (((f ⁻¹ᵁ W).ι.appIso U).inv.hom
        (((f ⁻¹ᵁ W).toScheme.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
          (((f.app W) ≫ (f ⁻¹ᵁ W).topIso.inv).hom r))) =
        (f.app V).hom ((T.presheaf.map (homOfLE hV).op).hom r) := by
  have hb : f.app W ≫ (f ⁻¹ᵁ W).topIso.inv ≫
      (f ⁻¹ᵁ W).toScheme.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫
        ((f ⁻¹ᵁ W).ι.appIso U).inv ≫ X.presheaf.map (eqToHom h.symm).op =
      T.presheaf.map (homOfLE hV).op ≫ f.app V := by
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv,
      Scheme.Opens.topIso_inv, Scheme.Opens.toScheme_presheaf_map]
    change f.app W ≫ X.presheaf.map (eqToHom (f ⁻¹ᵁ W).ι_image_top).op ≫
      X.presheaf.map (homOfLE (Scheme.Hom.image_mono (f ⁻¹ᵁ W).ι
        (le_top : U ≤ ⊤))).op ≫ X.presheaf.map (eqToHom h.symm).op = _
    simp only [← Functor.map_comp, ← op_comp]
    exact (f.naturality (homOfLE hV).op).symm
  exact ConcreteCategory.congr_hom hb r

private noncomputable def rawOpenIso {X T : Scheme.{u}}
    (f : X ⟶ T) {F : X.Modules} (I : InjectiveResolution F)
    (q : ℕ) (W V : T.Opens) (U : (f ⁻¹ᵁ W).toScheme.Opens)
    (h : (f ⁻¹ᵁ W).ι ''ᵁ U = f ⁻¹ᵁ V) :
    (RingedSpace.openModuleCohomology (f ⁻¹ᵁ W).toScheme.toRingedSpace q U).obj
        ((restrictFunctor (f ⁻¹ᵁ W).ι).obj F) ≅
      AddCommGrpCat.of ((sectionCohomologyPresheaf
        (((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex) q).obj (op V)) := by
  let Y := (f ⁻¹ᵁ W).toScheme
  let J := rawRestrictionResolution X (f ⁻¹ᵁ W) I
  let S := RingedSpace.openModuleSections Y.toRingedSpace U
  let : S.Additive := RingedSpace.openModuleSections_additive Y.toRingedSpace U
  let : (restrictFunctor (f ⁻¹ᵁ W).ι).Additive := ⟨by intros; rfl⟩
  let A := ((SheafOfModules.forget T.ringCatSheaf).mapHomologicalComplex (.up ℕ)).obj
    (((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
  let E := PresheafOfModules.toPresheaf T.ringCatSheaf.obj ⋙
    (CategoryTheory.evaluation T.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
  let : (RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)).Additive :=
    RingedSpace.openModuleSections_additive X.toRingedSpace (f ⁻¹ᵁ V)
  let eS : restrictFunctor (f ⁻¹ᵁ W).ι ⋙ S ≅
      RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V) :=
    restrictOpenSectionsIso X (f ⁻¹ᵁ W) U ≪≫
      sectionsCongr X h
  let eC : (S.mapHomologicalComplex (.up ℕ)).obj J.cocomplex ≅
      (E.mapHomologicalComplex (.up ℕ)).obj A :=
    (NatIso.mapHomologicalComplex eS (.up ℕ)).app I.cocomplex
  exact J.isoRightDerivedObj S q ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) q).mapIso eC ≪≫
      (A.sc q).mapHomologyIso E

private theorem rawOpenIso_scalar {X T : Scheme.{u}}
    (f : X ⟶ T) {F : X.Modules} (I : InjectiveResolution F)
    (q : ℕ) (W V : T.Opens) (hV : V ≤ W)
    (U : (f ⁻¹ᵁ W).toScheme.Opens) (h : (f ⁻¹ᵁ W).ι ''ᵁ U = f ⁻¹ᵁ V) :
    let P := sectionCohomologyPresheaf
      (((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex) q
    let : Module Γ(T, W) (P.obj (op V)) :=
      Module.compHom _ (T.presheaf.map (homOfLE hV).op).hom
    ∀ (r : Γ(T, W))
      (z : (RingedSpace.openModuleCohomology (f ⁻¹ᵁ W).toScheme.toRingedSpace q U).obj
        ((restrictFunctor (f ⁻¹ᵁ W).ι).obj F)),
      (rawOpenIso f I q W V U h).hom
        ((RingedSpace.openModuleCohomology (f ⁻¹ᵁ W).toScheme.toRingedSpace q U).map
          (scalarHom ((restrictFunctor (f ⁻¹ᵁ W).ι).obj F)
            (((f.app W) ≫ (f ⁻¹ᵁ W).topIso.inv).hom r)) z) =
        r • (show P.obj (op V) from (rawOpenIso f I q W V U h).hom z) := by
  dsimp only
  intro r z
  let Y := (f ⁻¹ᵁ W).toScheme
  let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
  let J := rawRestrictionResolution X (f ⁻¹ᵁ W) I
  let S := RingedSpace.openModuleSections Y.toRingedSpace U
  let : S.Additive := RingedSpace.openModuleSections_additive Y.toRingedSpace U
  let : (restrictFunctor (f ⁻¹ᵁ W).ι).Additive := ⟨by intros; rfl⟩
  let : (RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)).Additive :=
    RingedSpace.openModuleSections_additive X.toRingedSpace (f ⁻¹ᵁ V)
  let b := ((f.app W) ≫ (f ⁻¹ᵁ W).topIso.inv).hom r
  let rV := (T.presheaf.map (homOfLE hV).op).hom r
  let A := ((SheafOfModules.forget T.ringCatSheaf).mapHomologicalComplex (.up ℕ)).obj
    (((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
  let E := PresheafOfModules.toPresheaf T.ringCatSheaf.obj ⋙
    (CategoryTheory.evaluation T.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
  let eS : restrictFunctor (f ⁻¹ᵁ W).ι ⋙ S ≅
      RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V) :=
    restrictOpenSectionsIso X (f ⁻¹ᵁ W) U ≪≫ sectionsCongr X h
  let eC : (S.mapHomologicalComplex (.up ℕ)).obj J.cocomplex ≅
      (E.mapHomologicalComplex (.up ℕ)).obj A :=
    (NatIso.mapHomologicalComplex eS (.up ℕ)).app I.cocomplex
  let φ : J.cocomplex ⟶ J.cocomplex := {
    f := fun n ↦ scalarHom (J.cocomplex.X n) b
    comm' := fun i j _ ↦ (scalarHom_naturality (J.cocomplex.d i j) b).symm }
  have hφ : J.ι.f 0 ≫ φ.f 0 = scalarHom G b ≫ J.ι.f 0 :=
    scalarHom_naturality (J.ι.f 0) b
  let τ : E ⟶ E := {
    app := fun M ↦ ((M.obj (op V)).smul rV).asHom
    naturality := fun M N g ↦ by
      ext x
      exact ((g.app (op V)).hom.map_smul rV x).symm }
  have hc : (S.mapHomologicalComplex (.up ℕ)).map φ ≫ eC.hom =
      eC.hom ≫ (NatTrans.mapHomologicalComplex τ (.up ℕ)).app A := by
    apply HomologicalComplex.hom_ext
    intro n
    ext x
    change (I.cocomplex.X n).presheaf.map (eqToHom h.symm).op
      ((restrictAppIso (f ⁻¹ᵁ W).ι (I.cocomplex.X n) U).hom
        ((scalarHom (J.cocomplex.X n) b).app U x)) =
      (f.app V).hom rV • (I.cocomplex.X n).presheaf.map (eqToHom h.symm).op
        ((restrictAppIso (f ⁻¹ᵁ W).ι (I.cocomplex.X n) U).hom x)
    rw [scalarHom_app, smul_restrictAppIso_hom_apply, map_smul]
    rw [pullback_scalar_restrict f W V hV U h r]
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) q
  have hc' := congrArg
    ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u} (.up ℕ) q).map) hc
  simp only [Functor.map_comp] at hc'
  have hh := scalar_homology_transport
    (((S.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).sc q) (A.sc q) E
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) q).map
      ((S.mapHomologicalComplex (.up ℕ)).map φ))
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) q).map eC.hom) τ hc'
  have hn := J.isoRightDerivedObj_hom_naturality (scalarHom G b) J φ hφ S q
  have hh' : H.map ((S.mapHomologicalComplex (.up ℕ)).map φ) ≫ H.map eC.hom ≫
      ((A.sc q).mapHomologyIso E).hom = H.map eC.hom ≫
        ((A.sc q).mapHomologyIso E).hom ≫ τ.app (A.homology q) := hh
  have heq := congrArg
    (fun g ↦ g ≫ H.map eC.hom ≫ ((A.sc q).mapHomologyIso E).hom) hn
  simp only [Functor.comp_map, Category.assoc] at heq
  rw [hh'] at heq
  simpa only [rawOpenIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    ConcreteCategory.comp_apply, RingedSpace.openModuleCohomology, τ,
    ModuleCat.smul] using! ConcreteCategory.congr_hom heq z

private theorem homology_restriction_transport
    {C : Type*} [Category C] [Abelian C]
    (A A' : ShortComplex AddCommGrpCat.{u}) (B : ShortComplex C)
    (E E' : C ⥤ AddCommGrpCat.{u})
    [E.PreservesZeroMorphisms] [E.PreservesHomology]
    [E'.PreservesZeroMorphisms] [E'.PreservesHomology]
    (φ : A ⟶ A') (e : A ⟶ B.map E) (e' : A' ⟶ B.map E') (τ : E ⟶ E')
    (h : φ ≫ e' = e ≫ B.mapNatTrans τ) :
    ShortComplex.homologyMap φ ≫ ShortComplex.homologyMap e' ≫
        (B.mapHomologyIso E').hom =
      ShortComplex.homologyMap e ≫ (B.mapHomologyIso E).hom ≫ τ.app B.homology := by
  have hm := congrArg (fun g ↦ ShortComplex.homologyMap g) h
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp,
    ShortComplex.homologyMap_mapNatTrans] at hm
  have hm' := congrArg (fun g ↦ g ≫ (B.mapHomologyIso E').hom) hm
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hm'

private theorem rawOpenIso_restriction {X T : Scheme.{u}}
    (f : X ⟶ T) {F : X.Modules} (I : InjectiveResolution F)
    (q : ℕ) (W V : T.Opens) (hV : V ≤ W)
    (U : (f ⁻¹ᵁ W).toScheme.Opens) (h : (f ⁻¹ᵁ W).ι ''ᵁ U = f ⁻¹ᵁ V) :
    let P := sectionCohomologyPresheaf
      (((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex) q
    ∀ ξ : (RingedSpace.openModuleCohomology (f ⁻¹ᵁ W).toScheme.toRingedSpace q ⊤).obj
      ((restrictFunctor (f ⁻¹ᵁ W).ι).obj F),
      (rawOpenIso f I q W V U h).hom
        ((RingedSpace.openModuleCohomologyRestriction (f ⁻¹ᵁ W).toScheme.toRingedSpace q
          (homOfLE (le_top : U ≤ ⊤))).app ((restrictFunctor (f ⁻¹ᵁ W).ι).obj F) ξ) =
        (P.map (homOfLE hV).op).hom
          ((rawOpenIso f I q W W ⊤ (f ⁻¹ᵁ W).ι_image_top).hom ξ) := by
  dsimp only
  intro ξ
  let Y := (f ⁻¹ᵁ W).toScheme
  let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
  let J := rawRestrictionResolution X (f ⁻¹ᵁ W) I
  let ST := RingedSpace.openModuleSections Y.toRingedSpace ⊤
  let SU := RingedSpace.openModuleSections Y.toRingedSpace U
  let : ST.Additive := RingedSpace.openModuleSections_additive Y.toRingedSpace ⊤
  let : SU.Additive := RingedSpace.openModuleSections_additive Y.toRingedSpace U
  let : (restrictFunctor (f ⁻¹ᵁ W).ι).Additive := ⟨by intros; rfl⟩
  let : (RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ W)).Additive :=
    RingedSpace.openModuleSections_additive X.toRingedSpace (f ⁻¹ᵁ W)
  let : (RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)).Additive :=
    RingedSpace.openModuleSections_additive X.toRingedSpace (f ⁻¹ᵁ V)
  let A := ((SheafOfModules.forget T.ringCatSheaf).mapHomologicalComplex (.up ℕ)).obj
    (((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
  let ET := PresheafOfModules.toPresheaf T.ringCatSheaf.obj ⋙
    (CategoryTheory.evaluation T.Opensᵒᵖ AddCommGrpCat.{u}).obj (op W)
  let EU := PresheafOfModules.toPresheaf T.ringCatSheaf.obj ⋙
    (CategoryTheory.evaluation T.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
  let eST : restrictFunctor (f ⁻¹ᵁ W).ι ⋙ ST ≅
      RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ W) :=
    restrictOpenSectionsIso X (f ⁻¹ᵁ W) ⊤ ≪≫ sectionsCongr X (f ⁻¹ᵁ W).ι_image_top
  let eSU : restrictFunctor (f ⁻¹ᵁ W).ι ⋙ SU ≅
      RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V) :=
    restrictOpenSectionsIso X (f ⁻¹ᵁ W) U ≪≫ sectionsCongr X h
  let eCT : (ST.mapHomologicalComplex (.up ℕ)).obj J.cocomplex ≅
      (ET.mapHomologicalComplex (.up ℕ)).obj A :=
    (NatIso.mapHomologicalComplex eST (.up ℕ)).app I.cocomplex
  let eCU : (SU.mapHomologicalComplex (.up ℕ)).obj J.cocomplex ≅
      (EU.mapHomologicalComplex (.up ℕ)).obj A :=
    (NatIso.mapHomologicalComplex eSU (.up ℕ)).app I.cocomplex
  let α : ST ⟶ SU :=
    Functor.whiskerLeft (SheafOfModules.forget Y.ringCatSheaf ⋙
      PresheafOfModules.toPresheaf Y.ringCatSheaf.obj)
      ((CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).map
        (homOfLE (le_top : U ≤ ⊤)).op)
  let τ : ET ⟶ EU := Functor.whiskerLeft
    (PresheafOfModules.toPresheaf T.ringCatSheaf.obj)
    ((CategoryTheory.evaluation T.Opensᵒᵖ AddCommGrpCat.{u}).map (homOfLE hV).op)
  let φ := (NatTrans.mapHomologicalComplex α (.up ℕ)).app J.cocomplex
  have hc : φ ≫ eCU.hom = eCT.hom ≫
      (NatTrans.mapHomologicalComplex τ (.up ℕ)).app A := by
    apply HomologicalComplex.hom_ext
    intro n
    ext x
    change (I.cocomplex.X n).presheaf.map (eqToHom h.symm).op
      ((I.cocomplex.X n).presheaf.map
        (homOfLE (Scheme.Hom.image_mono (f ⁻¹ᵁ W).ι (le_top : U ≤ ⊤))).op x) =
      (I.cocomplex.X n).presheaf.map
        ((TopologicalSpace.Opens.map f.base).map (homOfLE hV)).op
        ((I.cocomplex.X n).presheaf.map (eqToHom (f ⁻¹ᵁ W).ι_image_top.symm).op x)
    simp only [← Functor.map_comp_apply, ← op_comp]
    congr 2
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) q
  have hc' := congrArg
    ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u} (.up ℕ) q).map) hc
  simp only [Functor.map_comp] at hc'
  have hh := homology_restriction_transport
    (((ST.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).sc q)
    (((SU.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).sc q) (A.sc q) ET EU
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) q).map φ)
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) q).map eCT.hom)
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) q).map eCU.hom) τ hc'
  have hn := J.rightDerived_app_eq α q
  have heq : (NatTrans.rightDerived α q).app G ≫ (J.isoRightDerivedObj SU q).hom =
      (J.isoRightDerivedObj ST q).hom ≫ H.map φ := by
    rw [hn]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have hh' : H.map φ ≫ H.map eCU.hom ≫ ((A.sc q).mapHomologyIso EU).hom =
      H.map eCT.hom ≫ ((A.sc q).mapHomologyIso ET).hom ≫ τ.app (A.homology q) := hh
  have heq' := congrArg
    (fun g ↦ g ≫ H.map eCU.hom ≫ ((A.sc q).mapHomologyIso EU).hom) heq
  simp only [Category.assoc] at heq'
  rw [hh'] at heq'
  simpa only [rawOpenIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    ConcreteCategory.comp_apply, RingedSpace.openModuleCohomologyRestriction,
    α, τ, sectionCohomologyPresheaf] using! ConcreteCategory.congr_hom heq' ξ


/-- Derived sections of the restricted coefficient sheaf agree with raw section
cohomology, preserving restriction and the action of every function on the base open.

Source: Stacks Project, Tag 01E4, Lemma 20.7.3 (section-complex computation), and
Tag 01E1 (restriction of injectives). This is the untwisted part of the proof of
`sectionCohomology_unit_comparisons`.
(blueprint: lem-pc-section-cohomology-untwisted-comparisons).

Proof: Restrict I termwise to Y = f inverse W. Exact restriction preserves
injectives, so the restricted augmented complex resolves G. The sectionwise
restrictAppIso identifies sections of this resolution on the top open with I
on f inverse W, hence with (f_* I)(W). The image of U in X is assumed to
be f inverse V. The same restrictAppIso therefore identifies sections on U
with (f_* I)(V). Apply isoRightDerivedObj for this one restricted resolution
and commute exact evaluation and scalar forgetting with homology. These
isomorphisms yield t and e. Naturality of isoRightDerivedObj for the section
restriction transformation, followed by naturality of mapHomologyIso, gives
the restriction equation. For any r in Gamma(T,W), the displayed coefficient
endomorphism is multiplication by the pullback of r: evaluate the inverse
right unitor, the tensor morphism and the right unitor on elementary tensors.
Lift this endomorphism to the restricted resolution using multiplication by
the same pullback in every degree; its augmentation square commutes by
linearity. Naturality of isoRightDerivedObj and the degreewise semilinear
section comparisons, proved by naturality of the pullback and linearity, identify its action
with multiplication by r restricted to V. This proves the scalar equation.
All maps exist for empty opens and zero sheaves; no invertibility of r
is used, and degree zero uses the same augmented resolution comparison. -/
theorem sectionCohomology_untwisted_comparisons {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) (I : InjectiveResolution F)
    (q : ℕ) (W V : T.Opens) (hV : V ≤ W) :
    let Y := (f ⁻¹ᵁ W).toScheme
    let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
    let L := 𝟙_ Y.Modules
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let P := sectionCohomologyPresheaf K q
    let : Module Γ(T, W) (P.obj (op V)) :=
      Module.compHom _ (T.presheaf.map (homOfLE hV).op).hom
    ∀ (U : Y.Opens), (f ⁻¹ᵁ W).ι ''ᵁ U = f ⁻¹ᵁ V →
      ∃ e : (RingedSpace.openModuleCohomology Y.toRingedSpace q U).obj G ≃+
          P.obj (op V),
      ∃ t : (RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).obj G ≃+
          P.obj (op W),
      (∀ (r : Γ(T, W)) (z : (RingedSpace.openModuleCohomology Y.toRingedSpace q U).obj G),
        e ((RingedSpace.openModuleCohomology Y.toRingedSpace q U).map
          ((ρ_ G).inv ≫ G ◁ homOfGlobalSection L
            (unitSectionsEquiv ⊤ (((f.app W) ≫ (f ⁻¹ᵁ W).topIso.inv).hom r)) ≫
              (ρ_ G).hom) z) = r • e z) ∧
      (∀ ξ : (RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).obj G,
        e ((RingedSpace.openModuleCohomologyRestriction Y.toRingedSpace q
          (homOfLE (le_top : U ≤ ⊤))).app G ξ) =
            (P.map (homOfLE hV).op).hom (t ξ)) := by
  dsimp only
  intro U h
  let eIso := rawOpenIso f I q W V U h
  let tIso := rawOpenIso f I q W W ⊤ (f ⁻¹ᵁ W).ι_image_top
  refine ⟨eIso.addCommGroupIsoToAddEquiv, tIso.addCommGroupIsoToAddEquiv, ?_, ?_⟩
  · intro r z
    exact rawOpenIso_scalar f I q W V hV U h r z
  · intro ξ
    exact rawOpenIso_restriction f I q W V hV U h ξ

end AlgebraicGeometry.Scheme.Modules
