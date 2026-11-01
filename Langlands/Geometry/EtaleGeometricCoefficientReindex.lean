import Langlands.Geometry.EtaleGeometricCoefficientDiagram

/-! # Reindexing geometric coefficients and actual cohomological diagrams -/

noncomputable section

universe u v w v' w' v'' w'' wS wR

namespace Langlands.Geometry.EtaleGeometricDiagram.CoefficientDiagram

open CategoryTheory AlgebraicGeometry
open EtaleInverseImage EtaleDerivedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type u} [CommRing R]
variable {J : Type v} [Category.{w} J] {S : J ⥤ Scheme.{u}ᵒᵖ}
variable {K : Type v'} [Category.{w'} K] (F : K ⥤ J)

/-- The geometric coefficient identity law with an explicit equality of
index arrows retained in its inverse-image constraint. -/
theorem map_id_transport (D : CoefficientDiagram R S) {i : J}
    (a : i ⟶ i) (h : a = 𝟙 i) :
    D.map a = (inverseImageCongr R
      (congrArg Quiver.Hom.unop ((congrArg S.map h).trans (S.map_id i))) ≪≫
        inverseImageId R (S.obj i).unop).hom.app (D.obj i) := by
  subst a
  exact D.map_id i

/-- The geometric composition law with an explicit equality of index
arrows retained in its inverse-image constraint. -/
theorem map_comp_transport (D : CoefficientDiagram R S) {i j k : J}
    (a : i ⟶ j) (b : j ⟶ k) (c : i ⟶ k) (h : c = a ≫ b) :
    (inverseImageComp R (S.map a).unop (S.map b).unop ≪≫
      inverseImageCongr R
        (congrArg Quiver.Hom.unop ((congrArg S.map h).trans (S.map_comp a b))).symm
          ).hom.app (D.obj i) ≫ D.map c =
      (diagramInverseImage R S b).map (D.map a) ≫ D.map b := by
  subst c
  exact D.map_comp a b

/-- Reindex actual module sheaves and geometric coefficient transitions
along any functor between index categories. -/
def reindex (D : CoefficientDiagram R S) : CoefficientDiagram R (F ⋙ S) where
  obj i := D.obj (F.obj i)
  map a := D.map (F.map a)
  map_id i := D.map_id_transport (F.map (𝟙 i)) (F.map_id i)
  map_comp a b := D.map_comp_transport (F.map a) (F.map b) (F.map (a ≫ b))
    (F.map_comp a b)

/-- Reindex coefficient morphisms by their actual component sheaf maps. -/
def reindexMap {D E : CoefficientDiagram R S} (α : D ⟶ E) :
    reindex F D ⟶ reindex F E where
  app i := α.app (F.obj i)
  comm a := α.comm (F.map a)

/-- Reindexing is a functor on geometric coefficient diagrams. -/
def reindexFunctor : CoefficientDiagram R S ⥤ CoefficientDiagram R (F ⋙ S) where
  obj := reindex F
  map := reindexMap F
  map_id D := by apply Hom.ext; rfl
  map_comp α β := by apply Hom.ext; rfl

/-- Evaluation after reindexing is evaluation at the image vertex. -/
def reindexEvaluationIso (i : K) :
    reindexFunctor (R := R) (S := S) F ⋙ evaluation i ≅ evaluation (F.obj i) :=
  Iso.refl _

/-- Identity reindexing is the identity functor on geometric coefficients. -/
def reindexIdIso :
    reindexFunctor (R := R) (S := S) (𝟭 J) ≅ 𝟭 (CoefficientDiagram R S) :=
  Iso.refl _

variable {L : Type v''} [Category.{w''} L] (H : L ⥤ K)

/-- Successive reindexing is reindexing along the composite index functor. -/
def reindexCompIso :
    reindexFunctor (R := R) (S := S) F ⋙ reindexFunctor H ≅ reindexFunctor (H ⋙ F) :=
  Iso.refl _

variable [∀ i : J, HasDerivedCategory.{wS} (ModuleSheaf (S.obj i).unop R)]
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

local instance : ∀ i : K, HasDerivedCategory.{wS}
    (ModuleSheaf ((F ⋙ S).obj i).unop R) :=
  fun i => inferInstanceAs
    (HasDerivedCategory.{wS} (ModuleSheaf (S.obj (F.obj i)).unop R))

/-- Derived sections of reindexed coefficients are the precomposed diagram. -/
theorem reindex_derivedSections (D : CoefficientDiagram R S) :
    (reindex F D).derivedSections = F ⋙ D.derivedSections := rfl

/-- Reindexing the actual derived-section diagram has identity components. -/
def reindexDerivedSectionsIso (D : CoefficientDiagram R S) :
    (reindex F D).derivedSections ≅ F ⋙ D.derivedSections :=
  Iso.refl _

/-- Derived-section reindexing is natural in compatible coefficients. -/
def reindexDerivedSectionsFunctorIso :
    reindexFunctor (R := R) (S := S) F ⋙ derivedSectionsFunctor ≅
      derivedSectionsFunctor ⋙
        (Functor.whiskeringLeft K J (DerivedCategory.Plus (ModuleCat.{u} R))).obj F :=
  NatIso.ofComponents (fun D => reindexDerivedSectionsIso F D)
    (fun α => by
      apply NatTrans.ext
      funext i
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Ordinary cohomology of reindexed coefficients is the precomposed diagram. -/
theorem reindex_cohomology (D : CoefficientDiagram R S) (q : ℕ) :
    (reindex F D).cohomology q = F ⋙ D.cohomology q := rfl

/-- Ordinary-cohomology reindexing has identity vertex maps. -/
def reindexCohomologyIso (D : CoefficientDiagram R S) (q : ℕ) :
    (reindex F D).cohomology q ≅ F ⋙ D.cohomology q :=
  Iso.refl _

/-- Ordinary-cohomology reindexing is natural in compatible coefficients. -/
def reindexCohomologyFunctorIso (q : ℕ) :
    reindexFunctor (R := R) (S := S) F ⋙ cohomologyFunctor q ≅
      cohomologyFunctor q ⋙ (Functor.whiskeringLeft K J (ModuleCat.{u} R)).obj F :=
  NatIso.ofComponents (fun D => reindexCohomologyIso F D q)
    (fun α => by
      apply NatTrans.ext
      funext i
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Actual sections of reindexed coefficients are the precomposed diagram. -/
theorem reindex_sections (D : CoefficientDiagram R S) :
    (reindex F D).sections = F ⋙ D.sections := rfl

/-- Section-diagram reindexing has identity vertex maps. -/
def reindexSectionsIso (D : CoefficientDiagram R S) :
    (reindex F D).sections ≅ F ⋙ D.sections :=
  Iso.refl _

/-- Section-diagram reindexing is natural in compatible coefficients. -/
def reindexSectionsFunctorIso :
    reindexFunctor (R := R) (S := S) F ⋙ sectionsFunctor ≅
      sectionsFunctor ⋙ (Functor.whiskeringLeft K J (ModuleCat.{u} R)).obj F :=
  NatIso.ofComponents (fun D => reindexSectionsIso F D)
    (fun α => by
      apply NatTrans.ext
      funext i
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The canonical homology comparison itself reindexes by precomposition. -/
theorem reindex_derivedSectionsHomologyIso (D : CoefficientDiagram R S) (q : ℕ) :
    derivedSectionsHomologyIso (reindex F D) q =
      Functor.isoWhiskerLeft F (derivedSectionsHomologyIso D q) := by
  apply Iso.ext
  apply NatTrans.ext
  rfl

/-- The canonical degree-zero comparison itself reindexes by precomposition. -/
theorem reindex_derivedSectionsZeroIso (D : CoefficientDiagram R S) :
    derivedSectionsZeroIso (reindex F D) =
      Functor.isoWhiskerLeft F (derivedSectionsZeroIso D) := by
  apply Iso.ext
  apply NatTrans.ext
  rfl

/-- The canonical comparison between ordinary degree zero and sections
also reindexes by precomposition. -/
theorem reindex_cohomologyZeroIso (D : CoefficientDiagram R S) :
    cohomologyZeroFunctorIso.app (reindex F D) =
      Functor.isoWhiskerLeft F (cohomologyZeroFunctorIso.app D) := by
  apply Iso.ext
  apply NatTrans.ext
  rfl

/-- Reindexing comparisons commute with canonical homology recovery. -/
theorem reindexDerivedSectionsIso_homology (D : CoefficientDiagram R S) (q : ℕ) :
    Functor.isoWhiskerRight (reindexDerivedSectionsIso F D)
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q) ≪≫
        Functor.isoWhiskerLeft F (derivedSectionsHomologyIso D q) =
      derivedSectionsHomologyIso (reindex F D) q ≪≫ reindexCohomologyIso F D q := by
  apply Iso.ext
  apply NatTrans.ext
  funext i
  change (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).map (𝟙 _) ≫
      (EtaleDerivedSectionsPlus.homologyNatIso (S.obj (F.obj i)).unop R q).hom.app
        (D.obj (F.obj i)) =
    (EtaleDerivedSectionsPlus.homologyNatIso (S.obj (F.obj i)).unop R q).hom.app
      (D.obj (F.obj i)) ≫ 𝟙 _
  simp

/-- Reindexing comparisons commute with canonical degree-zero recovery. -/
theorem reindexDerivedSectionsIso_zero (D : CoefficientDiagram R S) :
    Functor.isoWhiskerRight (reindexDerivedSectionsIso F D)
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0) ≪≫
        Functor.isoWhiskerLeft F (derivedSectionsZeroIso D) =
      derivedSectionsZeroIso (reindex F D) ≪≫ reindexSectionsIso F D := by
  apply Iso.ext
  apply NatTrans.ext
  funext i
  change (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map (𝟙 _) ≫
      (EtaleDerivedSectionsPlus.homologyZeroIso (S.obj (F.obj i)).unop R).hom.app
        (D.obj (F.obj i)) =
    (EtaleDerivedSectionsPlus.homologyZeroIso (S.obj (F.obj i)).unop R).hom.app
      (D.obj (F.obj i)) ≫ 𝟙 _
  simp

/-- The homology recovery square is natural in compatible coefficients. -/
theorem reindexDerivedSectionsFunctorIso_homology (q : ℕ) :
    Functor.isoWhiskerRight (reindexDerivedSectionsFunctorIso (R := R) (S := S) F)
        ((Functor.whiskeringRight K (DerivedCategory.Plus (ModuleCat.{u} R))
          (ModuleCat.{u} R)).obj
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q)) ≪≫
        Functor.isoWhiskerRight (derivedSectionsHomologyFunctorIso q)
          ((Functor.whiskeringLeft K J (ModuleCat.{u} R)).obj F) =
      Functor.isoWhiskerLeft (reindexFunctor F) (derivedSectionsHomologyFunctorIso q) ≪≫
        reindexCohomologyFunctorIso F q := by
  apply Iso.ext
  apply NatTrans.ext
  funext D
  exact congrArg Iso.hom (reindexDerivedSectionsIso_homology F D q)

/-- The degree-zero recovery square is natural in compatible coefficients. -/
theorem reindexDerivedSectionsFunctorIso_zero :
    Functor.isoWhiskerRight (reindexDerivedSectionsFunctorIso (R := R) (S := S) F)
        ((Functor.whiskeringRight K (DerivedCategory.Plus (ModuleCat.{u} R))
          (ModuleCat.{u} R)).obj
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0)) ≪≫
        Functor.isoWhiskerRight derivedSectionsZeroFunctorIso
          ((Functor.whiskeringLeft K J (ModuleCat.{u} R)).obj F) =
      Functor.isoWhiskerLeft (reindexFunctor F) derivedSectionsZeroFunctorIso ≪≫
        reindexSectionsFunctorIso F := by
  apply Iso.ext
  apply NatTrans.ext
  funext D
  exact congrArg Iso.hom (reindexDerivedSectionsIso_zero F D)

end Langlands.Geometry.EtaleGeometricDiagram.CoefficientDiagram
