import Langlands.Geometry.EtaleGeometricCoefficientReindex
import Langlands.Geometry.EtaleCohomologyReindex
import Langlands.Geometry.EtaleCoefficientComparisonRecovery

/-! # Coefficient transport under a change of index category -/

noncomputable section

universe u v w v' w' wS wR

namespace Langlands.Geometry

open CategoryTheory AlgebraicGeometry
open EtaleDerivedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type u} [CommRing R]
variable {J : Type v} [Category.{w} J] {S : J ⥤ Scheme.{u}ᵒᵖ}
variable [∀ {i j : J} (a : i ⟶ j), Etale (S.map a).unop]
variable {K : Type v'} [Category.{w'} K] (F : K ⥤ J)

namespace EtaleGeometricDiagram.CoefficientDiagram

/-- Reindexing restriction coefficients commutes with their geometric transport. -/
theorem reindex_ofRestriction (D : EtalePullback.CoefficientDiagram R S) :
    reindex F (ofRestriction D) =
      ofRestriction (EtalePullback.CoefficientDiagram.reindex F D) := rfl

/-- Reindexing geometric coefficients commutes with transport to restriction. -/
theorem reindex_toRestriction (D : CoefficientDiagram R S) :
    EtalePullback.CoefficientDiagram.reindex F (toRestriction D) =
      toRestriction (reindex F D) := rfl

/-- The two orders of restriction-to-geometric transport and reindexing
are naturally isomorphic, with identity component sheaf maps. -/
def reindexOfRestrictionIso :
    EtalePullback.CoefficientDiagram.reindexFunctor (R := R) (S := S) F ⋙
        ofRestrictionFunctor ≅
      ofRestrictionFunctor ⋙ reindexFunctor F :=
  Iso.refl _

/-- The two orders of geometric-to-restriction transport and reindexing
are naturally isomorphic, with identity component sheaf maps. -/
def reindexToRestrictionIso :
    reindexFunctor (R := R) (S := S) F ⋙ toRestrictionFunctor ≅
      toRestrictionFunctor ⋙ EtalePullback.CoefficientDiagram.reindexFunctor F :=
  Iso.refl _

/-- Reindexing preserves the specified geometric round-trip isomorphism. -/
theorem reindex_geometricRoundTripIso (D : CoefficientDiagram R S) :
    geometricRoundTripIso (reindex F D) =
      (reindexFunctor F).mapIso (geometricRoundTripIso D) := by
  apply Iso.ext
  apply Hom.ext
  rfl

/-- Reindexing preserves the specified restriction round-trip isomorphism. -/
theorem reindex_restrictionRoundTripIso (D : EtalePullback.CoefficientDiagram R S) :
    restrictionRoundTripIso (EtalePullback.CoefficientDiagram.reindex F D) =
      (EtalePullback.CoefficientDiagram.reindexFunctor F).mapIso
        (restrictionRoundTripIso D) := by
  apply Iso.ext
  apply EtalePullback.CoefficientDiagram.Hom.ext
  rfl

end EtaleGeometricDiagram.CoefficientDiagram

variable [∀ i : J, HasDerivedCategory.{wS} (ModuleSheaf (S.obj i).unop R)]
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

local instance : ∀ i : K, HasDerivedCategory.{wS}
    (ModuleSheaf ((F ⋙ S).obj i).unop R) :=
  fun i => inferInstanceAs
    (HasDerivedCategory.{wS} (ModuleSheaf (S.obj (F.obj i)).unop R))

namespace EtalePullback.CoefficientDiagram

/-- The actual restriction-derived diagram reindexes by precomposition. -/
theorem reindex_derivedSections (D : CoefficientDiagram R S) :
    (reindex F D).derivedSections = F ⋙ D.derivedSections := rfl

/-- The restriction-derived reindex comparison has identity vertex maps. -/
def reindexDerivedSectionsIso (D : CoefficientDiagram R S) :
    (reindex F D).derivedSections ≅ F ⋙ D.derivedSections :=
  Iso.refl _

/-- Restriction-derived reindexing is natural in compatible coefficients. -/
def reindexDerivedSectionsFunctorIso :
    reindexFunctor (R := R) (S := S) F ⋙ derivedSectionsFunctor ≅
      derivedSectionsFunctor ⋙
        (Functor.whiskeringLeft K J (DerivedCategory.Plus (ModuleCat.{u} R))).obj F :=
  NatIso.ofComponents (fun D => reindexDerivedSectionsIso F D)
    (fun α => by
      apply NatTrans.ext
      funext i
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

end EtalePullback.CoefficientDiagram

namespace EtaleGeometricDiagram.CoefficientDiagram

/-- The forward derived comparison itself reindexes by precomposition. -/
theorem reindex_ofRestrictionDerivedSectionsIso
    (D : EtalePullback.CoefficientDiagram R S) :
    ofRestrictionDerivedSectionsIso (EtalePullback.CoefficientDiagram.reindex F D) =
      Functor.isoWhiskerLeft F (ofRestrictionDerivedSectionsIso D) := by
  apply Iso.ext
  apply NatTrans.ext
  rfl

/-- The forward ordinary-cohomology comparison itself reindexes. -/
theorem reindex_ofRestrictionCohomologyIso
    (D : EtalePullback.CoefficientDiagram R S) (q : ℕ) :
    ofRestrictionCohomologyIso (EtalePullback.CoefficientDiagram.reindex F D) q =
      Functor.isoWhiskerLeft F (ofRestrictionCohomologyIso D q) := by
  apply Iso.ext
  apply NatTrans.ext
  rfl

/-- The forward actual-section comparison itself reindexes. -/
theorem reindex_ofRestrictionSectionsIso
    (D : EtalePullback.CoefficientDiagram R S) :
    ofRestrictionSectionsIso (EtalePullback.CoefficientDiagram.reindex F D) =
      Functor.isoWhiskerLeft F (ofRestrictionSectionsIso D) := by
  apply Iso.ext
  apply NatTrans.ext
  rfl

/-- The reverse derived comparison itself reindexes by precomposition. -/
theorem reindex_toRestrictionDerivedSectionsIso (D : CoefficientDiagram R S) :
    toRestrictionDerivedSectionsIso (reindex F D) =
      Functor.isoWhiskerLeft F (toRestrictionDerivedSectionsIso D) := by
  apply Iso.ext
  apply NatTrans.ext
  rfl

/-- The reverse ordinary-cohomology comparison itself reindexes. -/
theorem reindex_toRestrictionCohomologyIso (D : CoefficientDiagram R S) (q : ℕ) :
    toRestrictionCohomologyIso (reindex F D) q =
      Functor.isoWhiskerLeft F (toRestrictionCohomologyIso D q) := by
  apply Iso.ext
  apply NatTrans.ext
  rfl

/-- The reverse actual-section comparison itself reindexes. -/
theorem reindex_toRestrictionSectionsIso (D : CoefficientDiagram R S) :
    toRestrictionSectionsIso (reindex F D) =
      Functor.isoWhiskerLeft F (toRestrictionSectionsIso D) := by
  apply Iso.ext
  apply NatTrans.ext
  rfl

/-- Forward derived comparison commutes with the explicit reindex comparisons,
naturally in all compatible coefficients. -/
theorem reindex_ofRestrictionDerivedSectionsFunctorIso :
    Functor.isoWhiskerLeft
        (EtalePullback.CoefficientDiagram.reindexFunctor (R := R) (S := S) F)
        ofRestrictionDerivedSectionsFunctorIso ≪≫
        EtalePullback.CoefficientDiagram.reindexDerivedSectionsFunctorIso F =
      Functor.isoWhiskerRight (reindexOfRestrictionIso F) derivedSectionsFunctor ≪≫
        Functor.isoWhiskerLeft ofRestrictionFunctor
          (reindexDerivedSectionsFunctorIso F) ≪≫
        Functor.isoWhiskerRight ofRestrictionDerivedSectionsFunctorIso
          ((Functor.whiskeringLeft K J (DerivedCategory.Plus (ModuleCat.{u} R))).obj F) := by
  apply Iso.ext
  apply NatTrans.ext
  funext D
  apply NatTrans.ext
  funext i
  change 𝟙 _ ≫ 𝟙 _ =
    (EtaleDerivedSectionsPlus.derivedSections (S.obj (F.obj i)).unop R).map (𝟙 _) ≫
      𝟙 _ ≫ 𝟙 _
  simp

/-- The reverse derived comparison commutes with explicit reindexing,
naturally in coefficients. -/
theorem reindex_toRestrictionDerivedSectionsFunctorIso :
    Functor.isoWhiskerLeft (reindexFunctor (R := R) (S := S) F)
        toRestrictionDerivedSectionsFunctorIso ≪≫ reindexDerivedSectionsFunctorIso F =
      Functor.isoWhiskerRight (reindexToRestrictionIso F)
          EtalePullback.CoefficientDiagram.derivedSectionsFunctor ≪≫
        Functor.isoWhiskerLeft toRestrictionFunctor
          (EtalePullback.CoefficientDiagram.reindexDerivedSectionsFunctorIso F) ≪≫
        Functor.isoWhiskerRight toRestrictionDerivedSectionsFunctorIso
          ((Functor.whiskeringLeft K J (DerivedCategory.Plus (ModuleCat.{u} R))).obj F) := by
  apply Iso.ext
  apply NatTrans.ext
  funext D
  apply NatTrans.ext
  funext i
  change (toRestrictionDerivedSectionsIso (reindex F D)).hom.app i ≫ 𝟙 _ =
    (EtaleDerivedSectionsPlus.derivedSections (S.obj (F.obj i)).unop R).map (𝟙 _) ≫
      𝟙 _ ≫ (toRestrictionDerivedSectionsIso D).hom.app (F.obj i)
  simp only [toRestrictionDerivedSectionsIso_hom_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

/-- The reverse ordinary comparison commutes with explicit reindexing,
naturally in coefficients. -/
theorem reindex_toRestrictionCohomologyFunctorIso (q : ℕ) :
    Functor.isoWhiskerLeft (reindexFunctor (R := R) (S := S) F)
        (toRestrictionCohomologyFunctorIso q) ≪≫ reindexCohomologyFunctorIso F q =
      Functor.isoWhiskerRight (reindexToRestrictionIso F)
          (EtalePullback.CoefficientDiagram.cohomologyFunctor q) ≪≫
        Functor.isoWhiskerLeft toRestrictionFunctor
          (EtalePullback.CoefficientDiagram.reindexCohomologyFunctorIso F q) ≪≫
        Functor.isoWhiskerRight (toRestrictionCohomologyFunctorIso q)
          ((Functor.whiskeringLeft K J (ModuleCat.{u} R)).obj F) := by
  apply Iso.ext
  apply NatTrans.ext
  funext D
  apply NatTrans.ext
  funext i
  change (toRestrictionCohomologyIso (reindex F D) q).hom.app i ≫ 𝟙 _ =
    (EtaleDerivedSections.cohomology (S.obj (F.obj i)).unop R q).map (𝟙 _) ≫
      𝟙 _ ≫ (toRestrictionCohomologyIso D q).hom.app (F.obj i)
  simp only [toRestrictionCohomologyIso_hom_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

/-- The reverse actual-section comparison commutes with explicit reindexing,
naturally in coefficients. -/
theorem reindex_toRestrictionSectionsFunctorIso :
    Functor.isoWhiskerLeft (reindexFunctor (R := R) (S := S) F)
        toRestrictionSectionsFunctorIso ≪≫ reindexSectionsFunctorIso F =
      Functor.isoWhiskerRight (reindexToRestrictionIso F)
          EtalePullback.CoefficientDiagram.sectionsFunctor ≪≫
        Functor.isoWhiskerLeft toRestrictionFunctor
          (EtalePullback.CoefficientDiagram.reindexSectionsFunctorIso F) ≪≫
        Functor.isoWhiskerRight toRestrictionSectionsFunctorIso
          ((Functor.whiskeringLeft K J (ModuleCat.{u} R)).obj F) := by
  apply Iso.ext
  apply NatTrans.ext
  funext D
  apply NatTrans.ext
  funext i
  change (toRestrictionSectionsIso (reindex F D)).hom.app i ≫ 𝟙 _ =
    (EtalePullback.CoefficientDiagram.sectionsFunctor.map (𝟙 _)).app i ≫
      𝟙 _ ≫ (toRestrictionSectionsIso D).hom.app (F.obj i)
  rw [CategoryTheory.Functor.map_id]
  simp only [toRestrictionSectionsIso_hom_app, NatTrans.id_app,
    Category.id_comp, Category.comp_id]
  rfl

end EtaleGeometricDiagram.CoefficientDiagram

end Langlands.Geometry
