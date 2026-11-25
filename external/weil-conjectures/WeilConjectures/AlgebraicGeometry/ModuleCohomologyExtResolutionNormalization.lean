/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
public import WeilConjectures.AlgebraicGeometry.Modules.Ext


public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturalityExtension
import WeilConjectures.AlgebraicGeometry.SchemeModulesEnoughInjectives
import WeilConjectures.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtStandardResolutionFormula

/-! # Computing the fixed comparison on arbitrary injective resolutions

Source: Stacks Project, Tags 03FD and 015E.
(blueprint: new-module-cohomology-ext-resolution-normalization)
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution

attribute [local instance] enoughInjectives

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev moduleSections (X : Scheme.{u}) :=
  RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙ forget₂ _ AddCommGrpCat.{u}

abbrev abelianSections (X : Scheme.{u}) :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)

/-- The concrete comparison from module cohomology to the sections of a resolution.
Source: Stacks Project, Tag 01DZ, injective-resolution computation. -/
def moduleResolutionIso (X : Scheme.{u}) {F : SheafOfModules.{u} (moduleRings X.toRingedSpace)}
    (I : InjectiveResolution F) (p : ℕ) :
    (forget₂ _ AddCommGrpCat.{u}).obj
      ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F) ≅
    (((moduleSections X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex).homology p := by
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  exact (forget₂ _ AddCommGrpCat.{u}).mapIso
    (I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) p) ≪≫
    (((RingedSpace.globalSectionsComplex I).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{u})).symm

set_option backward.isDefEq.respectTransparency false in
/-- The Ext comparison to sections of a specified module resolution, using the
forgotten augmentation and its canonical acyclic-resolution comparison.
Source: Stacks Project, Tags 03FD, 015E and 06XR. -/
def abelianResolutionIso (X : Scheme.{u}) {F : SheafOfModules.{u} (moduleRings X.toRingedSpace)}
    (I : InjectiveResolution F) (p : ℕ) :
    AddCommGrpCat.of (H F p) ≅
    (((moduleSections X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex).homology p := by
  let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
  let ι := (HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℕ) 0).inv.app F ≫
    (T.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
  have : QuasiIso ι := by
    dsimp only [ι]
    have : QuasiIso ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι) :=
      inferInstance
    exact quasiIso_comp _ _
  exact (Abelian.Ext.precompAddEquiv (terminalSourceIso X) (T.obj F) p).toAddCommGrpIso ≪≫
    siteSectionsObjIso (Opens.grothendieckTopology X) ⊤ (T.obj F) p ≪≫
    (abelianSections X).rightDerivedObjIsoOfResolution ι
      (fun n ↦ forgottenInjectiveAcyclic X (I.cocomplex.X n)) p

private theorem moduleResolutionIso_naturality
    (X : Scheme.{u}) {F : SheafOfModules.{u} (moduleRings X.toRingedSpace)}
    (I J : InjectiveResolution F) (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = J.ι.f 0) (p : ℕ) :
    (moduleResolutionIso X I p).hom ≫
      HomologicalComplex.homologyMap
        (((moduleSections X).mapHomologicalComplex (.up ℕ)).map φ) p =
      (moduleResolutionIso X J p).hom := by
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let G := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let V := forget₂ (ModuleCat.{u}
    ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat.{u}
  have hd := congrArg V.map
    (I.isoRightDerivedObj_hom_naturality (𝟙 F) J φ (by simpa using hφ) G p)
  simp only [Functor.map_comp] at hd
  rw [(G.rightDerived p).map_id, V.map_id, Category.id_comp] at hd
  have hh := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ p).map
      ((G.mapHomologicalComplex (.up ℕ)).map φ)) V
  change V.map (HomologicalComplex.homologyMap
      ((G.mapHomologicalComplex (.up ℕ)).map φ) p) ≫
      ((((G.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).sc p).mapHomologyIso V).inv =
    ((((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).sc p).mapHomologyIso V).inv ≫
      HomologicalComplex.homologyMap
        (((moduleSections X).mapHomologicalComplex (.up ℕ)).map φ) p at hh
  dsimp only [moduleResolutionIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  simp only [Category.assoc]
  change V.map (I.isoRightDerivedObj G p).hom ≫ _ ≫ _ =
    V.map (J.isoRightDerivedObj G p).hom ≫ _
  erw [← hh]
  rw [← Category.assoc]
  change V.map (J.isoRightDerivedObj G p).hom =
    V.map (I.isoRightDerivedObj G p).hom ≫
      V.map (HomologicalComplex.homologyMap
        ((G.mapHomologicalComplex (.up ℕ)).map φ) p) at hd
  erw [← hd]
  rfl


private theorem abelianResolutionIso_inv_naturality
    (X : Scheme.{u}) {F : SheafOfModules.{u} (moduleRings X.toRingedSpace)}
    (I J : InjectiveResolution F) (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι ≫ φ = J.ι) (p : ℕ) :
    HomologicalComplex.homologyMap
        (((moduleSections X).mapHomologicalComplex (.up ℕ)).map φ) p ≫
      (abelianResolutionIso X J p).inv = (abelianResolutionIso X I p).inv := by
  let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
  let ιI := (HomologicalComplex.singleMapHomologicalComplex T (.up ℕ) 0).inv.app F ≫
    (T.mapHomologicalComplex (.up ℕ)).map I.ι
  let ιJ := (HomologicalComplex.singleMapHomologicalComplex T (.up ℕ) 0).inv.app F ≫
    (T.mapHomologicalComplex (.up ℕ)).map J.ι
  have : QuasiIso ιI := by
    dsimp only [ιI]
    have : QuasiIso ((T.mapHomologicalComplex (.up ℕ)).map I.ι) := inferInstance
    exact quasiIso_comp _ _
  have : QuasiIso ιJ := by
    dsimp only [ιJ]
    have : QuasiIso ((T.mapHomologicalComplex (.up ℕ)).map J.ι) := inferInstance
    exact quasiIso_comp _ _
  have hw : ιI ≫ (T.mapHomologicalComplex (.up ℕ)).map φ =
      (CochainComplex.single₀ _).map (𝟙 (T.obj F)) ≫ ιJ := by
    rw [(CochainComplex.single₀ _).map_id, Category.id_comp]
    simp only [ιI, ιJ, Category.assoc,
      ← Functor.map_comp, hφ]
  have hc := acyclicComparison_naturality (abelianSections X) (ιI) (ιJ)
    (fun n ↦ forgottenInjectiveAcyclic X (I.cocomplex.X n))
    (fun n ↦ forgottenInjectiveAcyclic X (J.cocomplex.X n))
    (𝟙 (T.obj F)) ((T.mapHomologicalComplex (.up ℕ)).map φ) hw p
  rw [((abelianSections X).rightDerived p).map_id, Category.comp_id] at hc
  change HomologicalComplex.homologyMap
      (((moduleSections X).mapHomologicalComplex (.up ℕ)).map φ) p ≫
      ((abelianSections X).rightDerivedObjIsoOfResolution (ιJ)
        (fun n ↦ forgottenInjectiveAcyclic X (J.cocomplex.X n)) p).inv =
    ((abelianSections X).rightDerivedObjIsoOfResolution (ιI)
      (fun n ↦ forgottenInjectiveAcyclic X (I.cocomplex.X n)) p).inv at hc
  dsimp only [abelianResolutionIso, Iso.trans_inv]
  simp only [Category.assoc]
  erw [reassoc_of% hc]


private theorem standardResolution_equiv
    (X : Scheme.{u}) (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace))] (p : ℕ)
    (x : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F) :
    moduleCohomologyExtResolutionEquiv X F p x =
      (abelianResolutionIso X (injectiveResolution F) p).inv
        ((moduleResolutionIso X (injectiveResolution F) p).hom x) := by
  let I : InjectiveResolution F := injectiveResolution F
  let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
  let ι := (HomologicalComplex.singleMapHomologicalComplex T (.up ℕ) 0).inv.app F ≫
    (T.mapHomologicalComplex (.up ℕ)).map I.ι
  have hι : QuasiIso ι := by
    dsimp only [ι]
    have : QuasiIso ((T.mapHomologicalComplex (.up ℕ)).map I.ι) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology I.ι T
    exact quasiIso_comp _ _
  exact standard_resolution_formula X F I rfl hι p
    (moduleResolutionIso X I p) (abelianResolutionIso X I p) (by rfl) (by rfl) x

set_option backward.isDefEq.respectTransparency false in
/-- The fixed comparison can be computed on any injective module resolution.
Source: Stacks Project, Tag 015E, naturality of acyclic-resolution comparisons;
Tag 03FD, acyclicity of forgotten injective modules.
(blueprint: new-module-cohomology-ext-resolution-normalization)

Proof: Lift the identity from I to the standard module resolution J. Naturality
of isoRightDerivedObj and of exact forgetting of homology makes the module
comparison commute with the section homology of this lift. Apply
acyclicComparison_naturality to the forgotten lift and augmentations: their
terms are section-acyclic by forgottenInjectiveAcyclic. Its inverse comparison
commutes with the same section homology map. Compose the two equations to
identify moduleResolutionIso followed by inverse abelianResolutionIso for I
and J. Evaluate the standard-resolution formula and apply the inverse-hom
identity for abelianResolutionIso on I. No invertibility assertion for the
section homology map is needed. The argument includes p=0, empty schemes and
zero modules, and involves no scheme morphism or edge map. -/
theorem moduleCohomologyExtResolutionEquiv_normalization
    (X : Scheme.{u}) {F : SheafOfModules.{u} (moduleRings X.toRingedSpace)}
    (I : InjectiveResolution F) (p : ℕ)
    (x : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F) :
    (abelianResolutionIso X I p).hom (moduleCohomologyExtResolutionEquiv X F p x) =
      (moduleResolutionIso X I p).hom x := by
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let J := injectiveResolution F
  let φ := InjectiveResolution.desc (𝟙 F) J I
  have hφ : I.ι ≫ φ = J.ι := by simp [φ]
  have hφ₀ : I.ι.f 0 ≫ φ.f 0 = J.ι.f 0 := by
    simpa using HomologicalComplex.congr_hom hφ 0
  have ha := moduleResolutionIso_naturality X I J φ hφ₀ p
  have hb := abelianResolutionIso_inv_naturality X I J φ hφ p
  have he : (moduleResolutionIso X J p).hom ≫ (abelianResolutionIso X J p).inv =
      (moduleResolutionIso X I p).hom ≫ (abelianResolutionIso X I p).inv := by
    rw [← ha, Category.assoc, hb]
  have hstd := standardResolution_equiv X F p x
  have hx := ConcreteCategory.congr_hom he x
  change (abelianResolutionIso X J p).inv ((moduleResolutionIso X J p).hom x) =
    (abelianResolutionIso X I p).inv ((moduleResolutionIso X I p).hom x) at hx
  calc
    (abelianResolutionIso X I p).hom (moduleCohomologyExtResolutionEquiv X F p x) =
        (abelianResolutionIso X I p).hom
          ((abelianResolutionIso X I p).inv ((moduleResolutionIso X I p).hom x)) :=
      congrArg (fun z ↦ (abelianResolutionIso X I p).hom z) (hstd.trans hx)
    _ = (moduleResolutionIso X I p).hom x :=
      ConcreteCategory.congr_hom (abelianResolutionIso X I p).inv_hom_id _

end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
