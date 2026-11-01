import Langlands.Geometry.EtaleGeometricActionDiagram
import Langlands.Geometry.EtaleGeometricCoefficientReindex

/-! # Reindexing geometric action diagrams in levels and groups -/

noncomputable section

universe u v w v' w' t t' uC vC uA vA uB vB wS wR

namespace Langlands.Geometry.EtaleGeometricDiagram

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Prod

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section Categorical

variable {J : Type v} [Category.{w} J] {K : Type v'} [Category.{w'} K]
variable {G : Type t} [Monoid G] {H : Type t'} [Monoid H]
variable (F : K ⥤ J) (φ : H →* G) (C : Type uC) [Category.{vC} C]

/-- Select levels along F and restrict algebraic actions along φ. -/
def actionDiagramReindexFunctor : (J ⥤ Action C G) ⥤ (K ⥤ Action C H) :=
  (Functor.whiskeringLeft K J (Action C G)).obj F ⋙
    (Functor.whiskeringRight K (Action C G) (Action C H)).obj (Action.res C φ)

variable {C}

/-- Currying a product-reindexed diagram is canonically level selection
followed by restriction of its action. Underlying component maps are identities. -/
def actionDiagramReindexIso (E : (J × SingleObj G) ⥤ C) :
    (actionDiagramFunctor K H C).obj ((F.prod (SingleObj.mapHom H G φ)) ⋙ E) ≅
      (actionDiagramReindexFunctor F φ C).obj ((actionDiagramFunctor J G C).obj E) :=
  NatIso.ofComponents
    (fun i => Action.mkIso (Iso.refl _) (fun h => by
      change E.map (F.map (𝟙 i) ×ₘ φ h) ≫ 𝟙 _ =
        𝟙 _ ≫ E.map (𝟙 (F.obj i) ×ₘ φ h)
      rw [F.map_id]
      exact (Category.comp_id _).trans (Category.id_comp _).symm))
    (fun {i j} a => by
      apply Action.Hom.ext
      change E.map (F.map a ×ₘ φ 1) ≫ 𝟙 _ =
        𝟙 _ ≫ E.map (F.map a ×ₘ (1 : G))
      rw [φ.map_one]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The product-reindex comparison is natural in all diagram morphisms. -/
def actionDiagramReindexFunctorIso :
    (Functor.whiskeringLeft (K × SingleObj H) (J × SingleObj G) C).obj
        (F.prod (SingleObj.mapHom H G φ)) ⋙ actionDiagramFunctor K H C ≅
      actionDiagramFunctor J G C ⋙ actionDiagramReindexFunctor F φ C :=
  NatIso.ofComponents (fun E => actionDiagramReindexIso F φ E)
    (fun {E E'} α => by
      apply NatTrans.ext
      funext i
      apply Action.Hom.ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]

/-- Lift a natural product-diagram reindexing comparison to action diagrams. -/
def actionDiagramReindexLiftIso (r : A ⥤ B)
    (E : A ⥤ ((J × SingleObj G) ⥤ C))
    (E' : B ⥤ ((K × SingleObj H) ⥤ C))
    (η : r ⋙ E' ≅ E ⋙
      (Functor.whiskeringLeft (K × SingleObj H) (J × SingleObj G) C).obj
        (F.prod (SingleObj.mapHom H G φ))) :
    r ⋙ (E' ⋙ actionDiagramFunctor K H C) ≅
      (E ⋙ actionDiagramFunctor J G C) ⋙ actionDiagramReindexFunctor F φ C :=
  Functor.isoWhiskerRight η (actionDiagramFunctor K H C) ≪≫
    Functor.isoWhiskerLeft E (actionDiagramReindexFunctorIso F φ)

/-- The lifted comparison first applies the supplied product-diagram
comparison, then the canonical level and group comparison. -/
theorem actionDiagramReindexLiftIso_app (r : A ⥤ B)
    (E : A ⥤ ((J × SingleObj G) ⥤ C))
    (E' : B ⥤ ((K × SingleObj H) ⥤ C))
    (η : r ⋙ E' ≅ E ⋙
      (Functor.whiskeringLeft (K × SingleObj H) (J × SingleObj G) C).obj
        (F.prod (SingleObj.mapHom H G φ))) (a : A) :
    (actionDiagramReindexLiftIso F φ r E E' η).app a =
      (actionDiagramFunctor K H C).mapIso (η.app a) ≪≫
        actionDiagramReindexIso F φ (E.obj a) := rfl

end Categorical

namespace CoefficientDiagram

open EtaleDerivedSections

variable {R : Type u} [CommRing R]
variable {J : Type v} [Category.{w} J] {K : Type v'} [Category.{w'} K]
variable {G : Type t} [Group G] {H : Type t'} [Group H]
variable {S : (J × SingleObj G) ⥤ Scheme.{u}ᵒᵖ}
variable (F : K ⥤ J) (φ : H →* G)
variable [∀ x : J × SingleObj G,
  HasDerivedCategory.{wS} (ModuleSheaf (S.obj x).unop R)]
variable [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

local instance : ∀ x : K × SingleObj H, HasDerivedCategory.{wS}
    (ModuleSheaf (((F.prod (SingleObj.mapHom H G φ)) ⋙ S).obj x).unop R) :=
  fun x => inferInstanceAs (HasDerivedCategory.{wS}
    (ModuleSheaf (S.obj ((F.prod (SingleObj.mapHom H G φ)).obj x)).unop R))

/-- Reindex actual geometric coefficients in levels and groups; the resulting
derived action diagram agrees canonically with level selection and restriction. -/
def reindexDerivedActionIso (D : CoefficientDiagram R S) :
    (reindex (F.prod (SingleObj.mapHom H G φ)) D).derivedAction ≅
      (actionDiagramReindexFunctor F φ _).obj D.derivedAction :=
  actionDiagramReindexIso F φ D.derivedSections

/-- The derived reindexing comparison has identity underlying components. -/
@[simp] theorem reindexDerivedActionIso_hom_app_hom
    (D : CoefficientDiagram R S) (i : K) :
    ((reindexDerivedActionIso F φ D).hom.app i).hom =
      𝟙 ((EtaleDerivedSectionsPlus.derivedSections
        (S.obj (F.obj i, SingleObj.star G)).unop R).obj
          (D.obj (F.obj i, SingleObj.star G))) := rfl

/-- Reindexing derived action diagrams is natural in compatible coefficients. -/
def reindexDerivedActionFunctorIso :
    reindexFunctor (R := R) (S := S) (F.prod (SingleObj.mapHom H G φ)) ⋙
        derivedActionFunctor ≅
      derivedActionFunctor ⋙ actionDiagramReindexFunctor F φ _ :=
  actionDiagramReindexLiftIso F φ _ derivedSectionsFunctor derivedSectionsFunctor
    (reindexDerivedSectionsFunctorIso (R := R) (S := S)
      (F.prod (SingleObj.mapHom H G φ)))

/-- The coefficient-natural derived comparison recovers the object comparison. -/
@[simp] theorem reindexDerivedActionFunctorIso_app (D : CoefficientDiagram R S) :
    (reindexDerivedActionFunctorIso F φ).app D = reindexDerivedActionIso F φ D := by
  unfold reindexDerivedActionFunctorIso
  rw [actionDiagramReindexLiftIso_app]
  change (actionDiagramFunctor K H _).mapIso (Iso.refl _) ≪≫ _ = _
  rw [Functor.mapIso_refl, Iso.refl_trans]
  rfl

/-- Ordinary cohomology action diagrams reindex canonically in levels and groups. -/
def reindexCohomologyActionIso (D : CoefficientDiagram R S) (q : ℕ) :
    (reindex (F.prod (SingleObj.mapHom H G φ)) D).cohomologyAction q ≅
      (actionDiagramReindexFunctor F φ _).obj (D.cohomologyAction q) :=
  actionDiagramReindexIso F φ (D.cohomology q)

/-- Ordinary-cohomology reindexing has identity underlying components. -/
@[simp] theorem reindexCohomologyActionIso_hom_app_hom
    (D : CoefficientDiagram R S) (q : ℕ) (i : K) :
    ((reindexCohomologyActionIso F φ D q).hom.app i).hom =
      𝟙 ((EtaleDerivedSections.cohomology
        (S.obj (F.obj i, SingleObj.star G)).unop R q).obj
          (D.obj (F.obj i, SingleObj.star G))) := rfl

/-- Ordinary-cohomology reindexing is natural in compatible coefficients. -/
def reindexCohomologyActionFunctorIso (q : ℕ) :
    reindexFunctor (R := R) (S := S) (F.prod (SingleObj.mapHom H G φ)) ⋙
        cohomologyActionFunctor q ≅
      cohomologyActionFunctor q ⋙ actionDiagramReindexFunctor F φ _ :=
  actionDiagramReindexLiftIso F φ _ (cohomologyFunctor q) (cohomologyFunctor q)
    (reindexCohomologyFunctorIso (R := R) (S := S)
      (F.prod (SingleObj.mapHom H G φ)) q)

/-- The coefficient-natural ordinary comparison recovers the object comparison. -/
@[simp] theorem reindexCohomologyActionFunctorIso_app
    (D : CoefficientDiagram R S) (q : ℕ) :
    (reindexCohomologyActionFunctorIso F φ q).app D =
      reindexCohomologyActionIso F φ D q := by
  unfold reindexCohomologyActionFunctorIso
  rw [actionDiagramReindexLiftIso_app]
  change (actionDiagramFunctor K H _).mapIso (Iso.refl _) ≪≫ _ = _
  rw [Functor.mapIso_refl, Iso.refl_trans]
  rfl

/-- Actual section action diagrams reindex canonically in levels and groups. -/
def reindexSectionsActionIso (D : CoefficientDiagram R S) :
    (reindex (F.prod (SingleObj.mapHom H G φ)) D).sectionsAction ≅
      (actionDiagramReindexFunctor F φ _).obj D.sectionsAction :=
  actionDiagramReindexIso F φ D.sections

/-- Section reindexing has identity underlying components. -/
@[simp] theorem reindexSectionsActionIso_hom_app_hom
    (D : CoefficientDiagram R S) (i : K) :
    ((reindexSectionsActionIso F φ D).hom.app i).hom =
      𝟙 ((EtaleDerivedSections.sections
        (S.obj (F.obj i, SingleObj.star G)).unop R).obj
          (D.obj (F.obj i, SingleObj.star G))) := rfl

/-- Section reindexing is natural in compatible coefficient morphisms. -/
def reindexSectionsActionFunctorIso :
    reindexFunctor (R := R) (S := S) (F.prod (SingleObj.mapHom H G φ)) ⋙
        sectionsActionFunctor ≅
      sectionsActionFunctor ⋙ actionDiagramReindexFunctor F φ _ :=
  actionDiagramReindexLiftIso F φ _ sectionsFunctor sectionsFunctor
    (reindexSectionsFunctorIso (R := R) (S := S)
      (F.prod (SingleObj.mapHom H G φ)))

/-- The coefficient-natural section comparison recovers the object comparison. -/
@[simp] theorem reindexSectionsActionFunctorIso_app (D : CoefficientDiagram R S) :
    (reindexSectionsActionFunctorIso F φ).app D = reindexSectionsActionIso F φ D := by
  unfold reindexSectionsActionFunctorIso
  rw [actionDiagramReindexLiftIso_app]
  change (actionDiagramFunctor K H _).mapIso (Iso.refl _) ≪≫ _ = _
  rw [Functor.mapIso_refl, Iso.refl_trans]
  rfl

/-- The full equivariant homology recovery square commutes with level and
group reindexing, retaining the existing canonical comparison maps. -/
theorem reindexDerivedActionIso_homology (D : CoefficientDiagram R S) (q : ℕ) :
    Functor.isoWhiskerRight (reindexDerivedActionIso F φ D)
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).mapAction H) ≪≫
        Functor.isoWhiskerLeft F
          (Functor.isoWhiskerRight (D.derivedActionHomologyIso q)
            (Action.res (ModuleCat.{u} R) φ)) =
      (reindex (F.prod (SingleObj.mapHom H G φ)) D).derivedActionHomologyIso q ≪≫
        reindexCohomologyActionIso F φ D q := by
  apply Iso.ext
  apply NatTrans.ext
  funext i
  apply Action.Hom.ext
  change (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).map (𝟙 _) ≫
      (EtaleDerivedSectionsPlus.homologyNatIso
        (S.obj (F.obj i, SingleObj.star G)).unop R q).hom.app
          (D.obj (F.obj i, SingleObj.star G)) =
    (EtaleDerivedSectionsPlus.homologyNatIso
      (S.obj (F.obj i, SingleObj.star G)).unop R q).hom.app
        (D.obj (F.obj i, SingleObj.star G)) ≫ 𝟙 _
  simp

/-- The full equivariant derived degree-zero recovery square commutes with
reindexing, using the specified canonical comparison with actual sections. -/
theorem reindexDerivedActionIso_zero (D : CoefficientDiagram R S) :
    Functor.isoWhiskerRight (reindexDerivedActionIso F φ D)
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction H) ≪≫
        Functor.isoWhiskerLeft F
          (Functor.isoWhiskerRight D.derivedActionZeroIso
            (Action.res (ModuleCat.{u} R) φ)) =
      (reindex (F.prod (SingleObj.mapHom H G φ)) D).derivedActionZeroIso ≪≫
        reindexSectionsActionIso F φ D := by
  apply Iso.ext
  apply NatTrans.ext
  funext i
  apply Action.Hom.ext
  change (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map (𝟙 _) ≫
      (EtaleDerivedSectionsPlus.homologyZeroIso
        (S.obj (F.obj i, SingleObj.star G)).unop R).hom.app
          (D.obj (F.obj i, SingleObj.star G)) =
    (EtaleDerivedSectionsPlus.homologyZeroIso
      (S.obj (F.obj i, SingleObj.star G)).unop R).hom.app
        (D.obj (F.obj i, SingleObj.star G)) ≫ 𝟙 _
  simp

/-- The equivariant ordinary degree-zero comparison is preserved by reindexing. -/
theorem reindexCohomologyActionIso_zero (D : CoefficientDiagram R S) :
    reindexCohomologyActionIso F φ D 0 ≪≫
        Functor.isoWhiskerLeft F
          (Functor.isoWhiskerRight (cohomologyActionZeroFunctorIso.app D)
            (Action.res (ModuleCat.{u} R) φ)) =
      cohomologyActionZeroFunctorIso.app
          (reindex (F.prod (SingleObj.mapHom H G φ)) D) ≪≫
        reindexSectionsActionIso F φ D := by
  apply Iso.ext
  apply NatTrans.ext
  funext i
  apply Action.Hom.ext
  change 𝟙 _ ≫
      ((EtaleDerivedSectionsPlus.homologyNatIso
        (S.obj (F.obj i, SingleObj.star G)).unop R 0).inv.app
          (D.obj (F.obj i, SingleObj.star G)) ≫
        (EtaleDerivedSectionsPlus.homologyZeroIso
          (S.obj (F.obj i, SingleObj.star G)).unop R).hom.app
            (D.obj (F.obj i, SingleObj.star G))) =
    ((EtaleDerivedSectionsPlus.homologyNatIso
      (S.obj (F.obj i, SingleObj.star G)).unop R 0).inv.app
        (D.obj (F.obj i, SingleObj.star G)) ≫
      (EtaleDerivedSectionsPlus.homologyZeroIso
        (S.obj (F.obj i, SingleObj.star G)).unop R).hom.app
          (D.obj (F.obj i, SingleObj.star G))) ≫ 𝟙 _
  simp


end CoefficientDiagram

end Langlands.Geometry.EtaleGeometricDiagram
