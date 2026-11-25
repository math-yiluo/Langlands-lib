/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Topology.Order
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.AlgebraicGeometry.RingedSpaceDirectImageKInjectiveAcyclic

/-!
# Unbounded direct images and the presheaf of local hypercohomology

Source: Stacks Project, Cohomology, Tags 0D5W and 0D5X, with Tag 0BKJ
(blueprint: lem-trf-unbounded-direct-image-section-presheaf).

Right deriving the entire presheaf of sections computes all evaluations on the same
K-injective representative. Exact evaluation and homology give H^q(U,E), and retain
all restrictions. The comparison is the unique map preserving the right-derived units.
The sheafification comparison is normalized on every K-injective representative.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

universe u wX wY

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

noncomputable section

/-- The ordinary abelian presheaf of sections, with the usual restriction maps.
Source: Stacks, Tags 0D5W and 0D5X
(blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
abbrev localAbelianSections (X : RingedSpace.{u}) :
    ringedSiteModules.{u} (moduleRings X) ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (moduleRings X) ⋙
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

/-- Standard localization of abelian presheaf complexes. This fixes only a size convention.
Source: Stacks, Tag 05RU (blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
instance localAbelianPresheaves_hasDerivedCategory (X : RingedSpace.{u}) :
    HasDerivedCategory ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  HasDerivedCategory.standard _

/-- The published K-injective replacement supplies the arbitrary-quasi-isomorphism
resolution hypothesis of the recorded total right-derived functor.
Source: Stacks, Tag 079P (blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
abbrev localSectionsEnoughKInjectives (X : RingedSpace.{u}) :
    ∀ K : CochainComplex (ringedSiteModules.{u} (moduleRings X)) ℤ,
      ∃ (I : CochainComplex (ringedSiteModules.{u} (moduleRings X)) ℤ) (s : K ⟶ I),
        I.IsKInjective ∧ QuasiIso s :=
  fun K ↦ ⟨(CochainComplex.kInjectiveResolutionFunctor.{u} _).obj K,
    (CochainComplex.toKInjectiveResolution.{u} _).app K, inferInstance,
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ K).2⟩

variable (X : RingedSpace.{u})
  [HasDerivedCategory.{wX} (ringedSiteModules.{u} (moduleRings X))]

/-- Unbounded derived sections on all opens simultaneously. Evaluation at U gives
RGamma(U,-): exact evaluation commutes with the localization, and this right-derived
functor is computed by evaluating the same K-injective representative at U.
Source: Stacks, Tags 0D5W and 0BKJ
(blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
abbrev derivedLocalAbelianSections :
    DerivedCategory (ringedSiteModules.{u} (moduleRings X)) ⥤
      DerivedCategory ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (localAbelianSections X).rightDerivedFunctorOfQuasiIsoResolutions
    (localSectionsEnoughKInjectives X)

/-- V maps to H^q(V,E). Homology in the abelian presheaf category is computed sectionwise;
its functor maps provide restriction and naturality for every derived morphism.
Source: Stacks, Tags 0D5W and 0D5X
(blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
abbrev localHypercohomologyPresheaf (q : ℤ) :
    DerivedCategory (ringedSiteModules.{u} (moduleRings X)) ⥤
      (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  derivedLocalAbelianSections X ⋙ DerivedCategory.homologyFunctor _ q

variable {X}
variable {Y : RingedSpace.{u}}
  [HasDerivedCategory.{wY} (ringedSiteModules.{u} (moduleRings Y))]

/-- Rf_* using the recorded universal-pair construction on K-injective representatives.
The ordinary direct image is the published moduleDirectImage, including f-sharp.
Source: Stacks, Tag 079V (blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
abbrev sectionDerivedDirectImage (f : X ⟶ Y) :
    DerivedCategory (ringedSiteModules.{u} (moduleRings X)) ⥤
      DerivedCategory (ringedSiteModules.{u} (moduleRings Y)) :=
  (moduleDirectImage f).rightDerivedFunctorOfQuasiIsoResolutions
    (localSectionsEnoughKInjectives X)

/-- The presheaf V maps to H^q(f^-1 V,E): right derive the actual inverse-image section
functor, whose underlying abelian groups and restrictions are literally F(f^-1 V).
Source: Stacks, Tag 0D5X (blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
abbrev inverseOpenHypercohomologyPresheaf (f : X ⟶ Y) (q : ℤ) :
    DerivedCategory (ringedSiteModules.{u} (moduleRings X)) ⥤
      (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (moduleDirectImage f ⋙ localAbelianSections Y).rightDerivedFunctorOfQuasiIsoResolutions
      (localSectionsEnoughKInjectives X) ⋙ DerivedCategory.homologyFunctor _ q

/-- The composite right-derived unit for f_* followed by sections. No assertion that f_*
preserves K-injectivity is used: for general ringed spaces the needed fact is acyclicity.
Source: Stacks, Tag 0D5W (blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
def localLerayCompositeUnit (f : X ⟶ Y) :
    (moduleDirectImage f ⋙ localAbelianSections Y).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (sectionDerivedDirectImage f ⋙ derivedLocalAbelianSections Y) :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (moduleDirectImage f ⋙ localAbelianSections Y)) (ComplexShape.up ℤ)).inv
      DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((moduleDirectImage f).mapHomotopyCategory (ComplexShape.up ℤ))
      ((localAbelianSections Y).rightDerivedFunctorOfQuasiIsoResolutionsUnit
        (localSectionsEnoughKInjectives Y)) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      ((moduleDirectImage f).rightDerivedFunctorOfQuasiIsoResolutionsUnit
        (localSectionsEnoughKInjectives X)) (derivedLocalAbelianSections Y) ≫
    (Functor.associator _ _ _).hom

/-- The unique canonical Leray comparison obtained from the universal bijection of the
recorded total right-derived functor. The choice is uniquely determined by its unit.
Source: Stacks, Tag 0D5W (blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
def localLerayComparison (f : X ⟶ Y) :
    (moduleDirectImage f ⋙ localAbelianSections Y).rightDerivedFunctorOfQuasiIsoResolutions
        (localSectionsEnoughKInjectives X) ⟶
      sectionDerivedDirectImage f ⋙ derivedLocalAbelianSections Y :=
  Classical.choose
    ((Functor.rightDerivedFunctorOfQuasiIsoResolutions_universal
      (moduleDirectImage f ⋙ localAbelianSections Y) (localSectionsEnoughKInjectives X)
        (sectionDerivedDirectImage f ⋙ derivedLocalAbelianSections Y)).surjective
      (localLerayCompositeUnit f))

/-- The canonical comparison on the two abelian presheaves, natural in the derived input.
Source: Stacks, Tags 0D5W and 0D5X
(blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
def localHypercohomologyComparison (f : X ⟶ Y) (q : ℤ) :
    inverseOpenHypercohomologyPresheaf f q ⟶
      sectionDerivedDirectImage f ⋙ localHypercohomologyPresheaf Y q :=
  Functor.whiskerRight (localLerayComparison f) (DerivedCategory.homologyFunctor _ q)

/-- The fixed, canonical sheafification comparison on a complex. Exact sheafification
commutes with homology, its counit recovers a sheaf, and forgetting modules is exact.
Source: Stacks, Tag 0BKJ (blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
def localSectionComplexSheafificationIso (Y : RingedSpace.{u}) (q : ℤ)
    (I : CochainComplex (ringedSiteModules.{u} (moduleRings Y)) ℤ) :
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
        ((((localAbelianSections Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homology q) ≅
      (SheafOfModules.toSheaf (moduleRings Y)).obj (I.homology q) :=
  let T := SheafOfModules.toSheaf (moduleRings Y)
  let U := sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
  let S := presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
  let e : (T ⋙ U) ⋙ S ≅ T :=
    Functor.associator T U S ≪≫
      Functor.isoWhiskerLeft T (asIso (sheafificationAdjunction _ _).counit) ≪≫
        T.rightUnitor
  (Functor.isoWhiskerLeft ((T ⋙ U).mapHomologicalComplex (ComplexShape.up ℤ))
      (S.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) q).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) q) ≪≫
    T.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) q).app I

/-- Normalization of the sheafification isomorphism on any K-injective representative.
The three factors are the right-derived unit, ordinary exact sheafification, and the
localization's homology comparison. Thus this specifies an isomorphism uniquely.
Source: Stacks, Tags 0BKJ and 0D5X
(blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
def localHypercohomologySheafificationModel (q : ℤ)
    (I : CochainComplex (ringedSiteModules.{u} (moduleRings Y)) ℤ) [I.IsKInjective] :
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
        ((localHypercohomologyPresheaf Y q).obj (DerivedCategory.Q.obj I)) ≅
      (SheafOfModules.toSheaf (moduleRings Y)).obj
        ((DerivedCategory.homologyFunctor _ q).obj (DerivedCategory.Q.obj I)) :=
  (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).mapIso
      ((DerivedCategory.homologyFunctor _ q).mapIso
          ((localAbelianSections Y).rightDerivedFunctorOfQuasiIsoResolutionsObjIso
            (localSectionsEnoughKInjectives Y) (𝟙 I)) ≪≫
        (DerivedCategory.homologyFunctorFactors _ q).app
          (((localAbelianSections Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≪≫
    localSectionComplexSheafificationIso Y q I ≪≫
    (SheafOfModules.toSheaf (moduleRings Y)).mapIso
      ((DerivedCategory.homologyFunctorFactors _ q).app I).symm

/-- The same normalized sheafification comparison at any derived object. A chosen complex
representative and its published K-injective replacement merely compute the canonical map;
the natural isomorphism below is required to agree with these components.
Source: Stacks, Tag 0BKJ (blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
def localHypercohomologySheafificationAt (q : ℤ)
    (M : DerivedCategory (ringedSiteModules.{u} (moduleRings Y))) :
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
        ((localHypercohomologyPresheaf Y q).obj M) ≅
      (SheafOfModules.toSheaf (moduleRings Y)).obj
        ((DerivedCategory.homologyFunctor _ q).obj M) :=
  let K := DerivedCategory.Q.objPreimage M
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u} _).obj K
  let s := (CochainComplex.toKInjectiveResolution.{u} _).app K
  letI : QuasiIso s :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ K).2
  let a : DerivedCategory.Q.obj I ≅ M :=
    (asIso (DerivedCategory.Q.map s)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso M
  (localHypercohomologyPresheaf Y q ⋙
      presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).mapIso a.symm ≪≫
    localHypercohomologySheafificationModel q I ≪≫
    (DerivedCategory.homologyFunctor _ q ⋙ SheafOfModules.toSheaf (moduleRings Y)).mapIso a

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Keep proof elaboration at the derived-functor API rather than its chosen construction.
attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  Functor.rightDerivedFunctorOfQuasiIsoResolutions
  Functor.rightDerivedFunctorOfQuasiIsoResolutionsUnit

-- A map to the Sierpiński space records one open, without changing its sections.

private def sectionTestSpace (Y : RingedSpace.{u}) (V : Opens Y) : RingedSpace.{u} where
  carrier := TopCat.of (ULift.{u} Prop)
  presheaf := (TopCat.Presheaf.pushforward CommRingCat
    (TopCat.ofHom ⟨fun y ↦ ULift.up (y ∈ V),
      continuous_uliftUp.comp (continuous_Prop.mpr V.isOpen)⟩)).obj Y.presheaf
  IsSheaf := TopCat.Sheaf.pushforward_sheaf_of_sheaf _ Y.IsSheaf

private def sectionTestMap (Y : RingedSpace.{u}) (V : Opens Y) :
    Y ⟶ sectionTestSpace Y V :=
  ⟨{ base := TopCat.ofHom ⟨fun y ↦ ULift.up (y ∈ V),
      continuous_uliftUp.comp (continuous_Prop.mpr V.isOpen)⟩, c := 𝟙 _ }⟩

private def sectionTestOpen : Opens (ULift.{u} Prop) :=
  ⟨{p | p.down}, continuous_uliftDown.isOpen_preimage _
    (continuous_Prop.mp continuous_id)⟩

private theorem sectionTestOpen_minimal (W : Opens (ULift.{u} Prop))
    (h : (ULift.up True : ULift.{u} Prop) ∈ W) : sectionTestOpen ≤ W := by
  intro p hp
  have e : p = ULift.up True := by
    apply ULift.ext
    exact propext ⟨fun _ ↦ trivial, fun _ ↦ hp⟩
  simpa only [e] using h

private theorem sectionTestGerm_isIso (F : (TopCat.of (ULift.{u} Prop)).Presheaf
    AddCommGrpCat.{u}) :
    IsIso (TopCat.Presheaf.germ F sectionTestOpen (ULift.up True) trivial) := by
  let n : OpenNhds (X := TopCat.of (ULift.{u} Prop)) (ULift.up True) := ⟨sectionTestOpen, trivial⟩
  have hn : IsInitial n := IsInitial.ofUniqueHom
    (fun W ↦ homOfLE (sectionTestOpen_minimal W.val W.property))
    (fun _ _ ↦ Subsingleton.elim _ _)
  exact isIso_ι_of_isTerminal hn.op _

private def sectionTestEvaluationIso (Y : RingedSpace.{u}) (V : Opens Y) :
    localAbelianSections (sectionTestSpace Y V) ⋙ (evaluation _ AddCommGrpCat.{u}).obj
        (op sectionTestOpen) ≅
      SheafOfModules.toSheaf (moduleRings (sectionTestSpace Y V)) ⋙
        sheafToPresheaf (Opens.grothendieckTopology (sectionTestSpace Y V))
          AddCommGrpCat.{u} ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (ULift.up True) := by
  let Z := sectionTestSpace Y V
  exact NatIso.ofComponents (fun M ↦
    @asIso AddCommGrpCat.{u} _ _ _
      (TopCat.Presheaf.germ ((localAbelianSections Z).obj M)
        sectionTestOpen (ULift.up True) trivial)
      (sectionTestGerm_isIso ((localAbelianSections Z).obj M))) (by
        intro M N a
        exact (TopCat.Presheaf.stalkFunctor_map_germ _ _ _
          ((localAbelianSections Z).map a)).symm)

omit [HasDerivedCategory.{wX} (ringedSiteModules.{u} (moduleRings X))] in
private theorem directImage_resolution_quasiIso
    {Z : RingedSpace.{u}}
    [HasDerivedCategory (SheafOfModules.{u} (moduleRings Z))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) [I.IsKInjective]
    (J : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ) [J.IsKInjective]
    (r : ((moduleDirectImage f).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso r] :
    QuasiIso (((moduleDirectImage g).mapHomologicalComplex (.up ℤ)).map r) := by
  let G := moduleDirectImage g
  let π := HomotopyCategory.quotient (SheafOfModules.{u} (moduleRings Y)) (.up ℤ)
  have hB : IsIso (G.rightDerivedFunctorUnit.app (π.obj
      (((moduleDirectImage f).mapHomologicalComplex (.up ℤ)).obj I))) :=
    isIso_moduleDirectImage_unit_on_kInjective f g I
  have hJ : IsIso (G.rightDerivedFunctorUnit.app (π.obj J)) := inferInstance
  have hr : IsIso (DerivedCategory.Qh.map (π.map r)) := by
    apply (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso _) r).mpr
    infer_instance
  have hn := G.rightDerivedFunctorUnit.naturality (π.map r)
  have hp : IsIso ((G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map
      (π.map r) ≫ G.rightDerivedFunctorUnit.app (π.obj J)) := by
    rw [hn]
    dsimp only [Functor.comp_map]
    infer_instance
  have hi : IsIso ((G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map
      (π.map r)) :=
    IsIso.of_isIso_comp_right _ (G.rightDerivedFunctorUnit.app (π.obj J))
  have hq : IsIso (DerivedCategory.Q.map
      ((G.mapHomologicalComplex (.up ℤ)).map r)) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso _)
      ((G.mapHomologicalComplex (.up ℤ)).map r)).mp hi
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hq

omit [HasDerivedCategory.{wX} (ringedSiteModules.{u} (moduleRings X))] in
private theorem localSections_directImage_resolution_quasiIso
    (f : X ⟶ Y)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) [I.IsKInjective]
    (J : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ) [J.IsKInjective]
    (r : ((moduleDirectImage f).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso r] :
    QuasiIso (((localAbelianSections Y).mapHomologicalComplex (.up ℤ)).map r) := by
  apply (HomologicalComplex.quasiIso_iff_evaluation _).mpr
  rintro ⟨V⟩
  let Z := sectionTestSpace Y V
  let g := sectionTestMap Y V
  let _ := HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings Z))
  have h := directImage_resolution_quasiIso f g I J r
  let E := localAbelianSections Z ⋙ (evaluation _ AddCommGrpCat.{u}).obj (op sectionTestOpen)
  let e := sectionTestEvaluationIso Y V
  let St := sheafToPresheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (ULift.up True)
  have : PreservesFiniteLimits St := inferInstanceAs
    (PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat.{u}
      (TopCat.of (ULift.{u} Prop)) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (ULift.up True)))
  have : PreservesFiniteColimits St := inferInstanceAs
    (PreservesFiniteColimits (TopCat.Sheaf.forget AddCommGrpCat.{u}
      (TopCat.of (ULift.{u} Prop)) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (ULift.up True)))
  have : PreservesFiniteLimits (SheafOfModules.toSheaf (moduleRings Z) ⋙ St) := inferInstance
  have : PreservesFiniteColimits (SheafOfModules.toSheaf (moduleRings Z) ⋙ St) := inferInstance
  have : PreservesFiniteLimits E := preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteColimits E := preservesFiniteColimits_of_natIso e.symm
  have hE : QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map
      (((moduleDirectImage g).mapHomologicalComplex (.up ℤ)).map r)) := by
    let _ := h
    infer_instance
  convert hE using 1 <;> rfl

omit [HasDerivedCategory.{wX} (ringedSiteModules.{u} (moduleRings X))] in
private theorem localSections_unit_directImage_isIso (f : X ⟶ Y)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) [I.IsKInjective] :
    IsIso (((localAbelianSections Y).rightDerivedFunctorOfQuasiIsoResolutionsUnit
      (localSectionsEnoughKInjectives Y)).app
        (((moduleDirectImage f).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj I))) := by
  let B := ((moduleDirectImage f).mapHomologicalComplex (.up ℤ)).obj I
  let J := (CochainComplex.kInjectiveResolutionFunctor.{u} _).obj B
  let r := (CochainComplex.toKInjectiveResolution.{u} _).app B
  let π := HomotopyCategory.quotient (SheafOfModules.{u} (moduleRings Y)) (.up ℤ)
  let G := localAbelianSections Y
  let η := G.rightDerivedFunctorOfQuasiIsoResolutionsUnit (localSectionsEnoughKInjectives Y)
  have : QuasiIso r :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ B).2
  have hG := localSections_directImage_resolution_quasiIso f I J r
  have hr : IsIso (DerivedCategory.Qh.map (π.map r)) := by
    apply (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso _) r).mpr
    infer_instance
  have hrG : IsIso (DerivedCategory.Qh.map
      ((G.mapHomotopyCategory (.up ℤ)).map (π.map r))) := by
    apply (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso _)
      ((G.mapHomologicalComplex (.up ℤ)).map r)).mpr
    let _ := hG
    infer_instance
  have hJ : IsIso (η.app (π.obj J)) :=
    G.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso (localSectionsEnoughKInjectives Y) J
  have hp : IsIso (η.app (π.obj B) ≫
      (G.rightDerivedFunctorOfQuasiIsoResolutions (localSectionsEnoughKInjectives Y)).map
        (DerivedCategory.Qh.map (π.map r))) := by
    have hn := η.naturality (π.map r)
    simp only [Functor.comp_map, Functor.id_obj] at hn
    rw [← hn]
    infer_instance
  change IsIso (η.app (π.obj B))
  exact IsIso.of_isIso_comp_right (η.app (π.obj B))
      ((G.rightDerivedFunctorOfQuasiIsoResolutions (localSectionsEnoughKInjectives Y)).map
        (DerivedCategory.Qh.map (π.map r)))

private theorem localLerayComparison_isIso (f : X ⟶ Y) :
    IsIso (localLerayComparison f) := by
  let FG := moduleDirectImage f ⋙ localAbelianSections Y
  let η := FG.rightDerivedFunctorOfQuasiIsoResolutionsUnit (localSectionsEnoughKInjectives X)
  have hfac : η ≫ Functor.whiskerLeft DerivedCategory.Qh (localLerayComparison f) =
      localLerayCompositeUnit f :=
    Classical.choose_spec
      ((Functor.rightDerivedFunctorOfQuasiIsoResolutions_universal
        (moduleDirectImage f ⋙ localAbelianSections Y) (localSectionsEnoughKInjectives X)
          (sectionDerivedDirectImage f ⋙ derivedLocalAbelianSections Y)).surjective
        (localLerayCompositeUnit f))
  have hI (I : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) [I.IsKInjective] :
      IsIso ((localLerayComparison f).app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj I))) := by
    have h₁ := localSections_unit_directImage_isIso f I
    have h₂ := (moduleDirectImage f).rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso
      (localSectionsEnoughKInjectives X) I
    have h₃ := FG.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso
      (localSectionsEnoughKInjectives X) I
    have hp : IsIso ((localLerayCompositeUnit f).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) := by
      dsimp only [localLerayCompositeUnit, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app]
      infer_instance
    have he := NatTrans.congr_app hfac ((HomotopyCategory.quotient _ (.up ℤ)).obj I)
    change η.app _ ≫ (localLerayComparison f).app _ = _ at he
    have hc : IsIso (η.app ((HomotopyCategory.quotient _ (.up ℤ)).obj I) ≫
        (localLerayComparison f).app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj I))) := by
      rw [he]
      exact hp
    exact IsIso.of_isIso_comp_left
      (η.app ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) _
  have hE (E : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
      IsIso ((localLerayComparison f).app E) := by
    let K := DerivedCategory.Q.objPreimage E
    let I := (CochainComplex.kInjectiveResolutionFunctor.{u} _).obj K
    let r := (CochainComplex.toKInjectiveResolution.{u} _).app K
    have : QuasiIso r :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ K).2
    let e := (DerivedCategory.Q.objObjPreimageIso E).symm ≪≫ asIso (DerivedCategory.Q.map r)
    let a : E ≅ DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj I) :=
      e ≪≫ ((DerivedCategory.quotientCompQhIso _).app I).symm
    have := hI I
    have hn := (localLerayComparison f).naturality a.hom
    have hp : IsIso ((localLerayComparison f).app E ≫
        (sectionDerivedDirectImage f ⋙ derivedLocalAbelianSections Y).map a.hom) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((sectionDerivedDirectImage f ⋙ derivedLocalAbelianSections Y).map a.hom)
  exact NatIso.isIso_of_isIso_app _

private theorem resolutionObjIso_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    {I J : CochainComplex C ℤ} [I.IsKInjective] [J.IsKInjective] (a : I ⟶ J) :
    (F.rightDerivedFunctorOfQuasiIsoResolutions h).map (DerivedCategory.Q.map a) ≫
        (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso h (𝟙 J)).hom =
      (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso h (𝟙 I)).hom ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a) := by
  let R := F.rightDerivedFunctorOfQuasiIsoResolutions h
  let η := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h
  let π := HomotopyCategory.quotient C (.up ℤ)
  have hI : IsIso (η.app (π.obj I)) :=
    F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso h I
  have hJ : IsIso (η.app (π.obj J)) :=
    F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso h J
  have he (K : CochainComplex C ℤ) [K.IsKInjective] [IsIso (η.app (π.obj K))] :
      (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso h (𝟙 K)).hom =
        (R.map ((DerivedCategory.quotientCompQhIso C).inv.app K) ≫
          inv (η.app (π.obj K))) ≫
          (DerivedCategory.quotientCompQhIso D).hom.app
            ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
    change R.map (DerivedCategory.Q.map (𝟙 K)) ≫
      (R.map ((DerivedCategory.quotientCompQhIso C).inv.app K) ≫
        inv (η.app (π.obj K)) ≫
          (DerivedCategory.quotientCompQhIso D).hom.app
            ((F.mapHomologicalComplex (.up ℤ)).obj K)) = _
    erw [DerivedCategory.Q.map_id, R.map_id, Category.id_comp, ← Category.assoc]
  have sq₁ : CommSq (DerivedCategory.Q.map a)
      ((DerivedCategory.quotientCompQhIso C).inv.app I)
      ((DerivedCategory.quotientCompQhIso C).inv.app J)
      (DerivedCategory.Qh.map (π.map a)) :=
    ⟨DerivedCategory.quotientCompQhIso_inv_naturality a⟩
  have su : CommSq (DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (.up ℤ)).map (π.map a)))
      (asIso (η.app (π.obj I))).hom (asIso (η.app (π.obj J))).hom
      (R.map (DerivedCategory.Qh.map (π.map a))) := ⟨η.naturality (π.map a)⟩
  have sq₃ : CommSq (DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (.up ℤ)).map (π.map a)))
      ((DerivedCategory.quotientCompQhIso D).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj I))
      ((DerivedCategory.quotientCompQhIso D).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj J))
      (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a)) :=
    ⟨DerivedCategory.quotientCompQhIso_hom_naturality
      ((F.mapHomologicalComplex (.up ℤ)).map a)⟩
  erw [he I, he J]
  exact (((sq₁.map R).vert_comp su.vert_inv).vert_comp sq₃).w

private def complexSheafificationIso (Y : RingedSpace.{u}) (q : ℤ) :
    (localAbelianSections Y).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor _ (.up ℤ) q ⋙
        presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ≅
      HomologicalComplex.homologyFunctor _ (.up ℤ) q ⋙
        SheafOfModules.toSheaf (moduleRings Y) :=
  let T := SheafOfModules.toSheaf (moduleRings Y)
  let U := sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
  let S := presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
  let e : (T ⋙ U) ⋙ S ≅ T :=
    Functor.associator T U S ≪≫
      Functor.isoWhiskerLeft T (asIso (sheafificationAdjunction _ _).counit) ≪≫
        T.rightUnitor
  Functor.isoWhiskerLeft ((T ⋙ U).mapHomologicalComplex (.up ℤ))
      (S.mapHomologicalComplexHomologyIso (.up ℤ) q).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso e (.up ℤ))
      (HomologicalComplex.homologyFunctor _ (.up ℤ) q) ≪≫
    T.mapHomologicalComplexHomologyIso (.up ℤ) q

private theorem sheafificationModel_naturality (q : ℤ)
    {I J : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ}
    [I.IsKInjective] [J.IsKInjective] (a : I ⟶ J) :
    (localHypercohomologyPresheaf Y q ⋙
        presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).map
        (DerivedCategory.Q.map a) ≫ (localHypercohomologySheafificationModel q J).hom =
      (localHypercohomologySheafificationModel q I).hom ≫
        (DerivedCategory.homologyFunctor _ q ⋙ SheafOfModules.toSheaf (moduleRings Y)).map
          (DerivedCategory.Q.map a) := by
  let F := localAbelianSections Y
  let S := presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
  let T := SheafOfModules.toSheaf (moduleRings Y)
  let H := DerivedCategory.homologyFunctor ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u}) q
  have h₁ := resolutionObjIso_naturality F (localSectionsEnoughKInjectives Y) a
  have h₂ := (DerivedCategory.homologyFunctorFactors
    ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u}) q).hom.naturality
      ((F.mapHomologicalComplex (.up ℤ)).map a)
  have h₃ := (complexSheafificationIso Y q).hom.naturality a
  have h₄ := (DerivedCategory.homologyFunctorFactors
    (SheafOfModules.{u} (moduleRings Y)) q).inv.naturality a
  dsimp only [Functor.comp_map] at h₂ h₃ h₄
  have hs₁ := congrArg (fun z ↦ S.map (H.map z)) h₁
  have hs₂ := congrArg S.map h₂
  have hs₄ := congrArg T.map h₄
  simp only [Functor.map_comp] at hs₁ hs₂ hs₄
  change S.map ((HomologicalComplex.homologyFunctor _ (.up ℤ) q).map
      ((F.mapHomologicalComplex (.up ℤ)).map a)) ≫
        (localSectionComplexSheafificationIso Y q J).hom =
      (localSectionComplexSheafificationIso Y q I).hom ≫
        T.map ((HomologicalComplex.homologyFunctor _ (.up ℤ) q).map a) at h₃
  have sq₁ := CommSq.mk hs₁
  have sq₂ := CommSq.mk hs₂
  have sq₃ := CommSq.mk h₃
  have sq₄ := CommSq.mk hs₄
  have hh := (((sq₁.vert_comp sq₂).vert_comp sq₃).vert_comp sq₄).w
  have he (K : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ)
      [K.IsKInjective] :
      (localHypercohomologySheafificationModel q K).hom =
        ((S.map (H.map ((F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
            (localSectionsEnoughKInjectives Y) (𝟙 K)).hom)) ≫
          S.map ((DerivedCategory.homologyFunctorFactors _ q).hom.app
            ((F.mapHomologicalComplex (.up ℤ)).obj K))) ≫
          (localSectionComplexSheafificationIso Y q K).hom) ≫
          T.map ((DerivedCategory.homologyFunctorFactors _ q).inv.app K) := by
    dsimp only [localHypercohomologySheafificationModel, Iso.trans, Functor.mapIso,
      Iso.symm, Iso.app_hom, Iso.app_inv]
    rw [S.map_comp]
    exact (Category.assoc _ _ _).symm
  rw [he I, he J]
  exact hh

private theorem exists_complex_map_into_kInjective
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (I J : CochainComplex C ℤ) [J.IsKInjective]
    (a : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj J) :
    ∃ b : I ⟶ J, DerivedCategory.Q.map b = a := by
  let e := DerivedCategory.quotientCompQhIso C
  obtain ⟨b, hb⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ (.up ℤ)).obj I) J).surjective
      (e.hom.app I ≫ a ≫ e.inv.app J)
  obtain ⟨b, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective b
  refine ⟨b, ?_⟩
  have hh := congrArg (fun z ↦ e.inv.app I ≫ z ≫ e.hom.app J) hb
  simpa [e, ← DerivedCategory.quotientCompQhIso_inv_naturality,
    -NatTrans.naturality] using hh

private theorem sheafificationAt_naturality (q : ℤ)
    {M N : DerivedCategory (SheafOfModules.{u} (moduleRings Y))} (a : M ⟶ N) :
    (localHypercohomologyPresheaf Y q ⋙
        presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).map a ≫
        (localHypercohomologySheafificationAt q N).hom =
      (localHypercohomologySheafificationAt q M).hom ≫
        (DerivedCategory.homologyFunctor _ q ⋙ SheafOfModules.toSheaf (moduleRings Y)).map a := by
  let C := SheafOfModules.{u} (moduleRings Y)
  let K (M : DerivedCategory C) := DerivedCategory.Q.objPreimage M
  let I (M : DerivedCategory C) := (CochainComplex.kInjectiveResolutionFunctor.{u} C).obj (K M)
  let r (M : DerivedCategory C) := (CochainComplex.toKInjectiveResolution.{u} C).app (K M)
  have hr (M : DerivedCategory C) : QuasiIso (r M) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} C (K M)).2
  let e (M : DerivedCategory C) : DerivedCategory.Q.obj (I M) ≅ M :=
    letI := hr M
    (asIso (DerivedCategory.Q.map (r M))).symm ≪≫ DerivedCategory.Q.objObjPreimageIso M
  let P := localHypercohomologyPresheaf Y q ⋙
    presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
  let G := DerivedCategory.homologyFunctor C q ⋙ SheafOfModules.toSheaf (moduleRings Y)
  obtain ⟨b, hb⟩ := exists_complex_map_into_kInjective (I M) (I N)
    ((e M).hom ≫ a ≫ (e N).inv)
  have hn := sheafificationModel_naturality q b
  change P.map (DerivedCategory.Q.map b) ≫
      (localHypercohomologySheafificationModel q (I N)).hom =
    (localHypercohomologySheafificationModel q (I M)).hom ≫
      G.map (DerivedCategory.Q.map b) at hn
  have ha : a = (e M).inv ≫ DerivedCategory.Q.map b ≫ (e N).hom := by
    simp [hb]
  change P.map a ≫ (P.map (e N).inv ≫
      (localHypercohomologySheafificationModel q (I N)).hom ≫ G.map (e N).hom) =
    (P.map (e M).inv ≫ (localHypercohomologySheafificationModel q (I M)).hom ≫
      G.map (e M).hom) ≫ G.map a
  rw [ha]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← P.map_comp_assoc (e N).hom (e N).inv,
    ← G.map_comp_assoc (e M).hom (e M).inv, Iso.hom_inv_id]
  simp only [P.map_id, G.map_id, Category.id_comp]
  rw [reassoc_of% hn]

/-- The local Leray comparison is an isomorphism of abelian presheaves in every integer
 degree, and sheafification is canonically the underlying abelian cohomology sheaf.
Both comparisons are natural in E; presheaf morphisms include all restriction squares.
The specified map and displayed K-injective normalization exclude arbitrary isomorphisms.
Source: Stacks, Tags 0D5W, 0D5X and 0BKJ
(blueprint: lem-trf-unbounded-direct-image-section-presheaf).

Proof:
1. For a K-injective complex I on X, resolve B=f_*I by r:B -> J on Y. Naturality of
   the right-derived unit, together with direct-image K-injective acyclicity, shows
   that g_*r is a quasi-isomorphism for any ringed-space map g:Y -> Z.
2. Classify an open V of Y by its continuous map to the Sierpiński space, equipped
   with the pushed-forward structure sheaf. Its open singleton has a least open
   neighborhood, so evaluation there is the stalk functor and is exact. Applied to
   the preceding quasi-isomorphism, this proves that sections of r on V are a
   quasi-isomorphism. Sectionwise detection gives the abelian-presheaf assertion.
3. Naturality makes the local-sections derived unit at B invertible. The defining
   universal-unit equation for localLerayComparison then makes it invertible on
   every K-injective representative, hence on every derived object. Taking homology
   gives the specified presheaf comparison, including every restriction square.
4. Naturality of the derived unit makes its inverse on K-injectives natural. Compose
   with the homology factorizations and exact sheafification to prove naturality of
   localHypercohomologySheafificationModel under chain maps of K-injectives.
5. Lift derived maps between the chosen K-injective representatives to chain maps
   using the K-injective Hom bijection and fullness of the homotopy quotient.
   Conjugating the preceding naturality square proves naturality of the exact
   components localHypercohomologySheafificationAt. Whisker by Rf_* to get s and
   compose with the sheafified presheaf comparison to get t.
No bound, scheme assumption or finiteness property is used. -/
theorem unboundedDirectImage_sectionPresheaf (f : X ⟶ Y) (q : ℤ) :
    ∃ e : inverseOpenHypercohomologyPresheaf f q ≅
        sectionDerivedDirectImage f ⋙ localHypercohomologyPresheaf Y q,
      e.hom = localHypercohomologyComparison f q ∧
        ∃ s : (sectionDerivedDirectImage f ⋙ localHypercohomologyPresheaf Y q) ⋙
            presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ≅
          sectionDerivedDirectImage f ⋙
            (DerivedCategory.homologyFunctor (ringedSiteModules.{u} (moduleRings Y)) q ⋙
              SheafOfModules.toSheaf (moduleRings Y)),
          (∀ E : DerivedCategory (ringedSiteModules.{u} (moduleRings X)),
            s.app E = localHypercohomologySheafificationAt q
              ((sectionDerivedDirectImage f).obj E)) ∧
          ∃ t : inverseOpenHypercohomologyPresheaf f q ⋙
              presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ≅
            sectionDerivedDirectImage f ⋙
              (DerivedCategory.homologyFunctor (ringedSiteModules.{u} (moduleRings Y)) q ⋙
                SheafOfModules.toSheaf (moduleRings Y)),
            t = Functor.isoWhiskerRight e
              (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) ≪≫ s := by
  have := localLerayComparison_isIso f
  let e : inverseOpenHypercohomologyPresheaf f q ≅
      sectionDerivedDirectImage f ⋙ localHypercohomologyPresheaf Y q :=
    Functor.isoWhiskerRight (asIso (localLerayComparison f))
      (DerivedCategory.homologyFunctor _ q)
  let s : localHypercohomologyPresheaf Y q ⋙
        presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ≅
      DerivedCategory.homologyFunctor _ q ⋙ SheafOfModules.toSheaf (moduleRings Y) :=
    NatIso.ofComponents (localHypercohomologySheafificationAt q)
      (fun a ↦ sheafificationAt_naturality q a)
  let s' := Functor.isoWhiskerLeft (sectionDerivedDirectImage f) s
  refine ⟨e, rfl, s', (fun _ ↦ rfl), ?_⟩
  exact ⟨Functor.isoWhiskerRight e
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) ≪≫ s', rfl⟩

end

end AlgebraicGeometry.RingedSpace
