import Langlands.Geometry.EtaleCanonicalDeckTower

/-! # Reindexing canonical cohomological consumers of over-base deck towers -/

noncomputable section

universe u v w v' w' t t' wS wR

set_option autoImplicit false

namespace Langlands.Geometry.EtaleCanonicalDeckTower

open CategoryTheory AlgebraicGeometry
open EtaleGeometricDiagram EtaleDerivedSections EtaleInverseImage
open scoped CategoryTheory.Prod

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme.{u}} {J : Type v} [Category.{w} J]
variable {G : Type t} [Group G]
variable (R : Type u) [CommRing R] (A : J ⥤ Action ((Over X)ᵒᵖ) G)
variable {K : Type v'} [Category.{w'} K] {H : Type t'} [Group H]
variable (F : K ⥤ J) (φ : H →* G)

/-- Canonical coefficients of the reindexed geometry are the reindexed
canonical coefficients of the original geometry. -/
theorem coefficientFunctor_reindex_eq :
    coefficientFunctor R (reindex A F φ) =
      coefficientFunctor R A ⋙
        CoefficientDiagram.reindexFunctor (F.prod (SingleObj.mapHom H G φ)) := rfl

variable [∀ x : J × SingleObj G,
  HasDerivedCategory.{wS} (ModuleSheaf ((schemeDiagram A).obj x).unop R)]
variable [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

local instance (i : J) :
    HasDerivedCategory.{wS} (ModuleSheaf (A.obj i).V.unop.left R) :=
  inferInstanceAs (HasDerivedCategory.{wS}
    (ModuleSheaf ((schemeDiagram A).obj (i, SingleObj.star G)).unop R))

local instance : ∀ x : K × SingleObj H, HasDerivedCategory.{wS}
    (ModuleSheaf ((schemeDiagram (reindex A F φ)).obj x).unop R) :=
  fun x => inferInstanceAs (HasDerivedCategory.{wS}
    (ModuleSheaf ((schemeDiagram A).obj
      ((F.prod (SingleObj.mapHom H G φ)).obj x)).unop R))

local instance : ∀ x : K × SingleObj H, HasDerivedCategory.{wS}
    (ModuleSheaf (((F.prod (SingleObj.mapHom H G φ)) ⋙ schemeDiagram A).obj x).unop R) :=
  fun x => inferInstanceAs (HasDerivedCategory.{wS}
    (ModuleSheaf ((schemeDiagram A).obj
      ((F.prod (SingleObj.mapHom H G φ)).obj x)).unop R))

/-- Name the reindexed consumer before constructing a comparison. -/
def reindexedDerivedFunctor :
    ModuleSheaf X R ⥤ (K ⥤ Action (DerivedCategory.Plus (ModuleCat.{u} R)) H) :=
  derivedFunctor R (reindex A F φ)

/-- Name level selection and group restriction of the original consumer. -/
def restrictedDerivedFunctor :
    ModuleSheaf X R ⥤ (K ⥤ Action (DerivedCategory.Plus (ModuleCat.{u} R)) H) :=
  derivedFunctor R A ⋙ actionDiagramReindexFunctor F φ _

/-- Keep the generic coefficient comparison's inferred endpoints intact. -/
def genericDerivedReindexIso :=
  Functor.isoWhiskerLeft (coefficientFunctor R A)
    (CoefficientDiagram.reindexDerivedActionFunctorIso F φ)

/-- Build the source comparison by mapping the coefficient comparison, then
using the explicit associator. -/
def derivedSourceIso :=
  Functor.isoWhiskerRight (reindexCoefficientFunctorIso R A F φ)
      CoefficientDiagram.derivedActionFunctor ≪≫
    Functor.associator (coefficientFunctor R A)
      (CoefficientDiagram.reindexFunctor (F.prod (SingleObj.mapHom H G φ)))
      CoefficientDiagram.derivedActionFunctor

private theorem derivedSourceIso_hom_app_app_hom
    (M : ModuleSheaf X R) (i : K) :
    (((derivedSourceIso R A F φ).hom.app M).app i).hom =
      𝟙 ((EtaleDerivedSectionsPlus.derivedSections (A.obj (F.obj i)).V.unop.left R).obj
        ((inverseImage (A.obj (F.obj i)).V.unop.hom R).obj M)) := by
  change (((CoefficientDiagram.derivedActionFunctor.map
    ((reindexCoefficientFunctorIso R A F φ).hom.app M)).app i).hom) ≫ 𝟙 _ = _
  rw [CoefficientDiagram.derivedActionFunctor_map_app_hom]
  rw [reindexCoefficientFunctorIso_hom_app_app]
  simp
  rfl

/-- Derived sections of the reindexed original geometry agree naturally with
level selection and group restriction of the original derived sections. -/
def reindexDerivedFunctorIso :
    reindexedDerivedFunctor R A F φ ≅ restrictedDerivedFunctor R A F φ :=
  derivedSourceIso R A F φ ≪≫
    genericDerivedReindexIso R A F φ ≪≫
      (Functor.associator (coefficientFunctor R A)
        CoefficientDiagram.derivedActionFunctor
        (actionDiagramReindexFunctor F φ _)).symm

/-- The generic comparison is identity on each original underlying object. -/
@[simp] theorem genericDerivedReindexIso_hom_app_app_hom
    (M : ModuleSheaf X R) (i : K) :
    (((genericDerivedReindexIso R A F φ).hom.app M).app i).hom =
      𝟙 ((EtaleDerivedSectionsPlus.derivedSections (A.obj (F.obj i)).V.unop.left R).obj
        ((inverseImage (A.obj (F.obj i)).V.unop.hom R).obj M)) := by
  have h := congrArg (fun e => (e.hom.app i).hom)
    (CoefficientDiagram.reindexDerivedActionFunctorIso_app F φ
      ((coefficientFunctor R A).obj M))
  exact h.trans (CoefficientDiagram.reindexDerivedActionIso_hom_app_hom F φ
    ((coefficientFunctor R A).obj M) i)

/-- The derived comparison is identity on each original underlying object. -/
@[simp] theorem reindexDerivedFunctorIso_hom_app_app_hom
    (M : ModuleSheaf X R) (i : K) :
    (((reindexDerivedFunctorIso R A F φ).hom.app M).app i).hom =
      𝟙 ((EtaleDerivedSectionsPlus.derivedSections (A.obj (F.obj i)).V.unop.left R).obj
        ((inverseImage (A.obj (F.obj i)).V.unop.hom R).obj M)) := by
  change (((derivedSourceIso R A F φ).hom.app M).app i).hom ≫
    (((genericDerivedReindexIso R A F φ).hom.app M).app i).hom ≫ 𝟙 _ = _
  rw [derivedSourceIso_hom_app_app_hom, genericDerivedReindexIso_hom_app_app_hom]
  simp
  exact Category.id_comp _

/-- Name the reindexed cohomology consumer. -/
def reindexedCohomologyFunctor (q : ℕ) :
    ModuleSheaf X R ⥤ (K ⥤ Action (ModuleCat.{u} R) H) :=
  cohomologyFunctor R (reindex A F φ) q

/-- Name level selection and restriction of the cohomology consumer. -/
def restrictedCohomologyFunctor (q : ℕ) :
    ModuleSheaf X R ⥤ (K ⥤ Action (ModuleCat.{u} R) H) :=
  cohomologyFunctor R A q ⋙ actionDiagramReindexFunctor F φ _

/-- The coefficient-natural cohomology comparison at canonical coefficients. -/
def genericCohomologyReindexIso (q : ℕ) :=
  Functor.isoWhiskerLeft (coefficientFunctor R A)
    (CoefficientDiagram.reindexCohomologyActionFunctorIso F φ q)

/-- Map the canonical coefficient comparison, then reassociate. -/
def cohomologySourceIso (q : ℕ) :=
  Functor.isoWhiskerRight (reindexCoefficientFunctorIso R A F φ)
      (CoefficientDiagram.cohomologyActionFunctor q) ≪≫
    Functor.associator (coefficientFunctor R A)
      (CoefficientDiagram.reindexFunctor (F.prod (SingleObj.mapHom H G φ)))
      (CoefficientDiagram.cohomologyActionFunctor q)

private theorem cohomologySourceIso_hom_app_app_hom (q : ℕ)
    (M : ModuleSheaf X R) (i : K) :
    (((cohomologySourceIso R A F φ q).hom.app M).app i).hom =
      𝟙 ((EtaleDerivedSections.cohomology (A.obj (F.obj i)).V.unop.left R q).obj
        ((inverseImage (A.obj (F.obj i)).V.unop.hom R).obj M)) := by
  change ((((CoefficientDiagram.cohomologyActionFunctor q).map
    ((reindexCoefficientFunctorIso R A F φ).hom.app M)).app i).hom) ≫ 𝟙 _ = _
  rw [CoefficientDiagram.cohomologyActionFunctor_map_app_hom]
  rw [reindexCoefficientFunctorIso_hom_app_app]
  simp
  rfl

/-- The original cohomology consumer commutes naturally with levels and groups. -/
def reindexCohomologyFunctorIso (q : ℕ) :
    reindexedCohomologyFunctor R A F φ q ≅ restrictedCohomologyFunctor R A F φ q :=
  cohomologySourceIso R A F φ q ≪≫
    genericCohomologyReindexIso R A F φ q ≪≫
      (Functor.associator (coefficientFunctor R A)
        (CoefficientDiagram.cohomologyActionFunctor q) (actionDiagramReindexFunctor F φ _)).symm

/-- The generic cohomology comparison has identity underlying components. -/
@[simp] theorem genericCohomologyReindexIso_hom_app_app_hom (q : ℕ)
    (M : ModuleSheaf X R) (i : K) :
    (((genericCohomologyReindexIso R A F φ q).hom.app M).app i).hom =
      𝟙 ((EtaleDerivedSections.cohomology (A.obj (F.obj i)).V.unop.left R q).obj
        ((inverseImage (A.obj (F.obj i)).V.unop.hom R).obj M)) := by
  have h := congrArg (fun e => (e.hom.app i).hom)
    (CoefficientDiagram.reindexCohomologyActionFunctorIso_app F φ
      ((coefficientFunctor R A).obj M) q)
  exact h.trans (CoefficientDiagram.reindexCohomologyActionIso_hom_app_hom F φ
    ((coefficientFunctor R A).obj M) q i)

/-- The cohomology comparison is identity on the original underlying object. -/
@[simp] theorem reindexCohomologyFunctorIso_hom_app_app_hom (q : ℕ)
    (M : ModuleSheaf X R) (i : K) :
    (((reindexCohomologyFunctorIso R A F φ q).hom.app M).app i).hom =
      𝟙 ((EtaleDerivedSections.cohomology (A.obj (F.obj i)).V.unop.left R q).obj
        ((inverseImage (A.obj (F.obj i)).V.unop.hom R).obj M)) := by
  change (((cohomologySourceIso R A F φ q).hom.app M).app i).hom ≫
    (((genericCohomologyReindexIso R A F φ q).hom.app M).app i).hom ≫ 𝟙 _ = _
  rw [cohomologySourceIso_hom_app_app_hom, genericCohomologyReindexIso_hom_app_app_hom]
  simp
  exact Category.id_comp _

/-- Name the reindexed sections consumer. -/
def reindexedSectionsFunctor :
    ModuleSheaf X R ⥤ (K ⥤ Action (ModuleCat.{u} R) H) :=
  sectionsFunctor R (reindex A F φ)

/-- Name level selection and restriction of the sections consumer. -/
def restrictedSectionsFunctor :
    ModuleSheaf X R ⥤ (K ⥤ Action (ModuleCat.{u} R) H) :=
  sectionsFunctor R A ⋙ actionDiagramReindexFunctor F φ _

/-- The coefficient-natural sections comparison at canonical coefficients. -/
def genericSectionsReindexIso :=
  Functor.isoWhiskerLeft (coefficientFunctor R A)
    (CoefficientDiagram.reindexSectionsActionFunctorIso F φ)

/-- Map the canonical coefficient comparison, then reassociate. -/
def sectionsSourceIso :=
  Functor.isoWhiskerRight (reindexCoefficientFunctorIso R A F φ)
      (CoefficientDiagram.sectionsActionFunctor) ≪≫
    Functor.associator (coefficientFunctor R A)
      (CoefficientDiagram.reindexFunctor (F.prod (SingleObj.mapHom H G φ)))
      (CoefficientDiagram.sectionsActionFunctor)

private theorem sectionsSourceIso_hom_app_app_hom
    (M : ModuleSheaf X R) (i : K) :
    (((sectionsSourceIso R A F φ).hom.app M).app i).hom =
      𝟙 ((EtaleDerivedSections.sections (A.obj (F.obj i)).V.unop.left R).obj
        ((inverseImage (A.obj (F.obj i)).V.unop.hom R).obj M)) := by
  change ((((CoefficientDiagram.sectionsActionFunctor).map
    ((reindexCoefficientFunctorIso R A F φ).hom.app M)).app i).hom) ≫ 𝟙 _ = _
  rw [CoefficientDiagram.sectionsActionFunctor_map_app_hom]
  rw [reindexCoefficientFunctorIso_hom_app_app]
  simp
  rfl

/-- The original sections consumer commutes naturally with levels and groups. -/
def reindexSectionsFunctorIso :
    reindexedSectionsFunctor R A F φ ≅ restrictedSectionsFunctor R A F φ :=
  sectionsSourceIso R A F φ ≪≫
    genericSectionsReindexIso R A F φ ≪≫
      (Functor.associator (coefficientFunctor R A)
        (CoefficientDiagram.sectionsActionFunctor) (actionDiagramReindexFunctor F φ _)).symm

/-- The generic sections comparison has identity underlying components. -/
@[simp] theorem genericSectionsReindexIso_hom_app_app_hom
    (M : ModuleSheaf X R) (i : K) :
    (((genericSectionsReindexIso R A F φ).hom.app M).app i).hom =
      𝟙 ((EtaleDerivedSections.sections (A.obj (F.obj i)).V.unop.left R).obj
        ((inverseImage (A.obj (F.obj i)).V.unop.hom R).obj M)) := by
  have h := congrArg (fun e => (e.hom.app i).hom)
    (CoefficientDiagram.reindexSectionsActionFunctorIso_app F φ
      ((coefficientFunctor R A).obj M))
  exact h.trans (CoefficientDiagram.reindexSectionsActionIso_hom_app_hom F φ
    ((coefficientFunctor R A).obj M) i)

/-- The sections comparison is identity on the original underlying object. -/
@[simp] theorem reindexSectionsFunctorIso_hom_app_app_hom
    (M : ModuleSheaf X R) (i : K) :
    (((reindexSectionsFunctorIso R A F φ).hom.app M).app i).hom =
      𝟙 ((EtaleDerivedSections.sections (A.obj (F.obj i)).V.unop.left R).obj
        ((inverseImage (A.obj (F.obj i)).V.unop.hom R).obj M)) := by
  change (((sectionsSourceIso R A F φ).hom.app M).app i).hom ≫
    (((genericSectionsReindexIso R A F φ).hom.app M).app i).hom ≫ 𝟙 _ = _
  rw [sectionsSourceIso_hom_app_app_hom, genericSectionsReindexIso_hom_app_app_hom]
  simp
  exact Category.id_comp _

/-- Homology recovery commutes with reindexing as an equality of equivariant
natural isomorphisms at every original base coefficient. -/
theorem reindexDerivedFunctorIso_homology
    (q : ℕ) (M : ModuleSheaf X R) :
    Functor.isoWhiskerRight ((reindexDerivedFunctorIso R A F φ).app M)
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).mapAction H) ≪≫
        Functor.isoWhiskerLeft F
          (Functor.isoWhiskerRight ((homologyFunctorIso R A q).app M)
            (Action.res (ModuleCat.{u} R) φ)) =
      (homologyFunctorIso R (reindex A F φ) q).app M ≪≫
        (reindexCohomologyFunctorIso R A F φ q).app M := by
  apply Iso.ext
  apply NatTrans.ext
  funext i
  apply Action.Hom.ext
  change (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).map
        (((reindexDerivedFunctorIso R A F φ).hom.app M).app i).hom ≫
      (((homologyFunctorIso R A q).hom.app M).app (F.obj i)).hom =
    (((homologyFunctorIso R (reindex A F φ) q).hom.app M).app i).hom ≫
      (((reindexCohomologyFunctorIso R A F φ q).hom.app M).app i).hom
  rw [reindexDerivedFunctorIso_hom_app_app_hom,
    reindexCohomologyFunctorIso_hom_app_app_hom]
  change (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).map (𝟙 _) ≫
      (EtaleDerivedSectionsPlus.homologyNatIso (A.obj (F.obj i)).V.unop.left R q).hom.app
        ((inverseImage (A.obj (F.obj i)).V.unop.hom R).obj M) =
    (EtaleDerivedSectionsPlus.homologyNatIso (A.obj (F.obj i)).V.unop.left R q).hom.app
        ((inverseImage (A.obj (F.obj i)).V.unop.hom R).obj M) ≫ 𝟙 _
  simp

/-- Derived degree-zero recovery retains the original canonical section
comparison after reindexing. -/
theorem reindexDerivedFunctorIso_zero (M : ModuleSheaf X R) :
    Functor.isoWhiskerRight ((reindexDerivedFunctorIso R A F φ).app M)
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction H) ≪≫
        Functor.isoWhiskerLeft F
          (Functor.isoWhiskerRight ((derivedZeroFunctorIso R A).app M)
            (Action.res (ModuleCat.{u} R) φ)) =
      (derivedZeroFunctorIso R (reindex A F φ)).app M ≪≫
        (reindexSectionsFunctorIso R A F φ).app M := by
  apply Iso.ext
  apply NatTrans.ext
  funext i
  apply Action.Hom.ext
  change (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
        (((reindexDerivedFunctorIso R A F φ).hom.app M).app i).hom ≫
      (((derivedZeroFunctorIso R A).hom.app M).app (F.obj i)).hom =
    (((derivedZeroFunctorIso R (reindex A F φ)).hom.app M).app i).hom ≫
      (((reindexSectionsFunctorIso R A F φ).hom.app M).app i).hom
  rw [reindexDerivedFunctorIso_hom_app_app_hom,
    reindexSectionsFunctorIso_hom_app_app_hom]
  change (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map (𝟙 _) ≫
      (EtaleDerivedSectionsPlus.homologyZeroIso (A.obj (F.obj i)).V.unop.left R).hom.app
        ((inverseImage (A.obj (F.obj i)).V.unop.hom R).obj M) =
    (EtaleDerivedSectionsPlus.homologyZeroIso (A.obj (F.obj i)).V.unop.left R).hom.app
        ((inverseImage (A.obj (F.obj i)).V.unop.hom R).obj M) ≫ 𝟙 _
  simp

/-- Ordinary degree-zero recovery retains its specified canonical comparison. -/
theorem reindexCohomologyFunctorIso_zero (M : ModuleSheaf X R) :
    (reindexCohomologyFunctorIso R A F φ 0).app M ≪≫
        Functor.isoWhiskerLeft F
          (Functor.isoWhiskerRight ((cohomologyZeroFunctorIso R A).app M)
            (Action.res (ModuleCat.{u} R) φ)) =
      (cohomologyZeroFunctorIso R (reindex A F φ)).app M ≪≫
        (reindexSectionsFunctorIso R A F φ).app M := by
  apply Iso.ext
  apply NatTrans.ext
  funext i
  apply Action.Hom.ext
  change (((reindexCohomologyFunctorIso R A F φ 0).hom.app M).app i).hom ≫
      (((cohomologyZeroFunctorIso R A).hom.app M).app (F.obj i)).hom =
    (((cohomologyZeroFunctorIso R (reindex A F φ)).hom.app M).app i).hom ≫
      (((reindexSectionsFunctorIso R A F φ).hom.app M).app i).hom
  rw [reindexCohomologyFunctorIso_hom_app_app_hom,
    reindexSectionsFunctorIso_hom_app_app_hom]
  change 𝟙 _ ≫ ((EtaleDerivedSectionsPlus.homologyNatIso (A.obj (F.obj i)).V.unop.left R 0).inv.app
        ((inverseImage (A.obj (F.obj i)).V.unop.hom R).obj M) ≫
      (EtaleDerivedSectionsPlus.homologyZeroIso (A.obj (F.obj i)).V.unop.left R).hom.app
        ((inverseImage (A.obj (F.obj i)).V.unop.hom R).obj M)) =
    ((EtaleDerivedSectionsPlus.homologyNatIso (A.obj (F.obj i)).V.unop.left R 0).inv.app
        ((inverseImage (A.obj (F.obj i)).V.unop.hom R).obj M) ≫
      (EtaleDerivedSectionsPlus.homologyZeroIso (A.obj (F.obj i)).V.unop.left R).hom.app
        ((inverseImage (A.obj (F.obj i)).V.unop.hom R).obj M)) ≫ 𝟙 _
  simp

end Langlands.Geometry.EtaleCanonicalDeckTower
