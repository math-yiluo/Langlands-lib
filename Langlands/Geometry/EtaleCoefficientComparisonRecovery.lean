import Langlands.Geometry.EtaleCoefficientDiagramComparison

/-! # Reverse coefficient comparisons and canonical cohomology recovery -/

noncomputable section

universe u v w wS wR

namespace Langlands.Geometry.EtaleGeometricDiagram.CoefficientDiagram

open CategoryTheory AlgebraicGeometry
open EtaleDerivedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type u} [CommRing R]
variable {J : Type v} [Category.{w} J] {S : J ⥤ Scheme.{u}ᵒᵖ}
variable [∀ {i j : J} (a : i ⟶ j), Etale (S.map a).unop]
variable [∀ i : J, HasDerivedCategory.{wS} (ModuleSheaf (S.obj i).unop R)]
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

/-- Transporting geometric coefficients to restriction preserves the actual
derived-section diagram. -/
def toRestrictionDerivedSectionsIso (D : CoefficientDiagram R S) :
    (toRestriction D).derivedSections ≅ D.derivedSections :=
  (ofRestrictionDerivedSectionsIso (toRestriction D)).symm ≪≫
    derivedSectionsFunctor.mapIso (geometricRoundTripIso D)

@[simp]
theorem toRestrictionDerivedSectionsIso_hom_app (D : CoefficientDiagram R S) (i : J) :
    (toRestrictionDerivedSectionsIso D).hom.app i = 𝟙 _ := by
  change 𝟙 _ ≫
    (EtaleDerivedSectionsPlus.derivedSections (S.obj i).unop R).map (𝟙 (D.obj i)) = 𝟙 _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- Reverse transport commutes with the derived-section diagram functor. -/
def toRestrictionDerivedSectionsFunctorIso :
    toRestrictionFunctor (R := R) (S := S) ⋙
        EtalePullback.CoefficientDiagram.derivedSectionsFunctor ≅ derivedSectionsFunctor :=
  NatIso.ofComponents toRestrictionDerivedSectionsIso
    (fun {D E} α => by
      apply NatTrans.ext
      funext i
      simp only [NatTrans.comp_app, toRestrictionDerivedSectionsIso_hom_app]
      change (EtaleDerivedSectionsPlus.derivedSections (S.obj i).unop R).map (α.app i) ≫
        𝟙 _ = 𝟙 _ ≫
          (EtaleDerivedSectionsPlus.derivedSections (S.obj i).unop R).map (α.app i)
      simp)

/-- Reverse transport preserves ordinary cohomology in every nonnegative degree. -/
def toRestrictionCohomologyIso (D : CoefficientDiagram R S) (q : ℕ) :
    (toRestriction D).cohomology q ≅ D.cohomology q :=
  (ofRestrictionCohomologyIso (toRestriction D) q).symm ≪≫
    (cohomologyFunctor q).mapIso (geometricRoundTripIso D)

@[simp]
theorem toRestrictionCohomologyIso_hom_app (D : CoefficientDiagram R S)
    (q : ℕ) (i : J) :
    (toRestrictionCohomologyIso D q).hom.app i = 𝟙 _ := by
  change 𝟙 _ ≫
    (EtaleDerivedSections.cohomology (S.obj i).unop R q).map (𝟙 (D.obj i)) = 𝟙 _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- Reverse ordinary-cohomology comparisons are natural in coefficients. -/
def toRestrictionCohomologyFunctorIso (q : ℕ) :
    toRestrictionFunctor (R := R) (S := S) ⋙
        EtalePullback.CoefficientDiagram.cohomologyFunctor q ≅ cohomologyFunctor q :=
  NatIso.ofComponents (fun D => toRestrictionCohomologyIso D q)
    (fun {D E} α => by
      apply NatTrans.ext
      funext i
      simp only [NatTrans.comp_app, toRestrictionCohomologyIso_hom_app]
      change (EtaleDerivedSections.cohomology (S.obj i).unop R q).map (α.app i) ≫
        𝟙 _ = 𝟙 _ ≫
          (EtaleDerivedSections.cohomology (S.obj i).unop R q).map (α.app i)
      simp)

/-- Reverse transport preserves actual global-section diagrams. -/
def toRestrictionSectionsIso (D : CoefficientDiagram R S) :
    (toRestriction D).sections ≅ D.sections :=
  (ofRestrictionSectionsIso (toRestriction D)).symm ≪≫
    sectionsFunctor.mapIso (geometricRoundTripIso D)

@[simp]
theorem toRestrictionSectionsIso_hom_app (D : CoefficientDiagram R S) (i : J) :
    (toRestrictionSectionsIso D).hom.app i = 𝟙 _ := by
  change 𝟙 _ ≫
    (EtaleDerivedSections.sections (S.obj i).unop R).map (𝟙 (D.obj i)) = 𝟙 _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- Reverse section comparisons are natural in compatible coefficients. -/
def toRestrictionSectionsFunctorIso :
    toRestrictionFunctor (R := R) (S := S) ⋙
        EtalePullback.CoefficientDiagram.sectionsFunctor ≅ sectionsFunctor :=
  NatIso.ofComponents toRestrictionSectionsIso
    (fun {D E} α => by
      apply NatTrans.ext
      funext i
      simp only [NatTrans.comp_app, toRestrictionSectionsIso_hom_app]
      change (EtalePullback.CoefficientDiagram.sectionsFunctor.map
        (toRestrictionFunctor.map α)).app i ≫ 𝟙 _ =
          𝟙 _ ≫ (EtaleDerivedSections.sections (S.obj i).unop R).map (α.app i)
      rw [EtalePullback.CoefficientDiagram.sectionsFunctor_map_app]
      simp [toRestrictionFunctor])

/-- Forward comparison commutes with the chosen recovery of ordinary cohomology. -/
theorem ofRestrictionDerivedSectionsIso_homology
    (D : EtalePullback.CoefficientDiagram R S) (q : ℕ) :
    Functor.isoWhiskerRight (ofRestrictionDerivedSectionsIso D)
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q) ≪≫
        EtalePullback.CoefficientDiagram.derivedSectionsHomologyIso D q =
      derivedSectionsHomologyIso (ofRestriction D) q ≪≫
        ofRestrictionCohomologyIso D q := by
  apply Iso.ext
  apply NatTrans.ext
  funext i
  change (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).map (𝟙 _) ≫
      (EtaleDerivedSectionsPlus.homologyNatIso (S.obj i).unop R q).hom.app (D.obj i) =
    (EtaleDerivedSectionsPlus.homologyNatIso (S.obj i).unop R q).hom.app (D.obj i) ≫ 𝟙 _
  simp

/-- Forward comparison commutes with canonical degree-zero recovery of sections. -/
theorem ofRestrictionDerivedSectionsIso_zero (D : EtalePullback.CoefficientDiagram R S) :
    Functor.isoWhiskerRight (ofRestrictionDerivedSectionsIso D)
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0) ≪≫
        EtalePullback.CoefficientDiagram.derivedSectionsZeroIso D =
      derivedSectionsZeroIso (ofRestriction D) ≪≫ ofRestrictionSectionsIso D := by
  apply Iso.ext
  apply NatTrans.ext
  funext i
  change (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map (𝟙 _) ≫
      ((EtaleDerivedSectionsPlus.homologyNatIso (S.obj i).unop R 0).hom.app (D.obj i) ≫
        (EtaleDerivedSections.cohomologyZeroIso (S.obj i).unop R).hom.app (D.obj i)) =
    ((EtaleDerivedSectionsPlus.homologyNatIso (S.obj i).unop R 0).hom.app (D.obj i) ≫
        (EtaleDerivedSections.cohomologyZeroIso (S.obj i).unop R).hom.app (D.obj i)) ≫ 𝟙 _
  simp

/-- Reverse comparison commutes with the same canonical homology recovery. -/
theorem toRestrictionDerivedSectionsIso_homology (D : CoefficientDiagram R S) (q : ℕ) :
    Functor.isoWhiskerRight (toRestrictionDerivedSectionsIso D)
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q) ≪≫
        derivedSectionsHomologyIso D q =
      EtalePullback.CoefficientDiagram.derivedSectionsHomologyIso (toRestriction D) q ≪≫
        toRestrictionCohomologyIso D q := by
  apply Iso.ext
  apply NatTrans.ext
  funext i
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, toRestrictionDerivedSectionsIso_hom_app,
    toRestrictionCohomologyIso_hom_app, Category.comp_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- Reverse comparison commutes with canonical degree-zero recovery of sections. -/
theorem toRestrictionDerivedSectionsIso_zero (D : CoefficientDiagram R S) :
    Functor.isoWhiskerRight (toRestrictionDerivedSectionsIso D)
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0) ≪≫
        derivedSectionsZeroIso D =
      EtalePullback.CoefficientDiagram.derivedSectionsZeroIso (toRestriction D) ≪≫
        toRestrictionSectionsIso D := by
  apply Iso.ext
  apply NatTrans.ext
  funext i
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, toRestrictionDerivedSectionsIso_hom_app,
    toRestrictionSectionsIso_hom_app, Category.comp_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- Forward homology recovery compatibility is itself natural in coefficients. -/
theorem ofRestrictionDerivedSectionsFunctorIso_homology (q : ℕ) :
    Functor.isoWhiskerRight (ofRestrictionDerivedSectionsFunctorIso (R := R) (S := S))
        ((Functor.whiskeringRight J (DerivedCategory.Plus (ModuleCat.{u} R))
          (ModuleCat.{u} R)).obj
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q)) ≪≫
        EtalePullback.CoefficientDiagram.derivedSectionsHomologyFunctorIso q =
      Functor.isoWhiskerLeft ofRestrictionFunctor (derivedSectionsHomologyFunctorIso q) ≪≫
        ofRestrictionCohomologyFunctorIso q := by
  apply Iso.ext
  apply NatTrans.ext
  funext D
  exact congrArg Iso.hom (ofRestrictionDerivedSectionsIso_homology D q)

/-- Forward degree-zero recovery compatibility is natural in coefficients. -/
theorem ofRestrictionDerivedSectionsFunctorIso_zero :
    Functor.isoWhiskerRight (ofRestrictionDerivedSectionsFunctorIso (R := R) (S := S))
        ((Functor.whiskeringRight J (DerivedCategory.Plus (ModuleCat.{u} R))
          (ModuleCat.{u} R)).obj
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0)) ≪≫
        EtalePullback.CoefficientDiagram.derivedSectionsZeroFunctorIso =
      Functor.isoWhiskerLeft ofRestrictionFunctor derivedSectionsZeroFunctorIso ≪≫
        ofRestrictionSectionsFunctorIso := by
  apply Iso.ext
  apply NatTrans.ext
  funext D
  exact congrArg Iso.hom (ofRestrictionDerivedSectionsIso_zero D)

/-- Reverse homology recovery compatibility is natural in coefficients. -/
theorem toRestrictionDerivedSectionsFunctorIso_homology (q : ℕ) :
    Functor.isoWhiskerRight (toRestrictionDerivedSectionsFunctorIso (R := R) (S := S))
        ((Functor.whiskeringRight J (DerivedCategory.Plus (ModuleCat.{u} R))
          (ModuleCat.{u} R)).obj
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q)) ≪≫
        derivedSectionsHomologyFunctorIso q =
      Functor.isoWhiskerLeft toRestrictionFunctor
          (EtalePullback.CoefficientDiagram.derivedSectionsHomologyFunctorIso q) ≪≫
        toRestrictionCohomologyFunctorIso q := by
  apply Iso.ext
  apply NatTrans.ext
  funext D
  exact congrArg Iso.hom (toRestrictionDerivedSectionsIso_homology D q)

/-- Reverse degree-zero recovery compatibility is natural in coefficients. -/
theorem toRestrictionDerivedSectionsFunctorIso_zero :
    Functor.isoWhiskerRight (toRestrictionDerivedSectionsFunctorIso (R := R) (S := S))
        ((Functor.whiskeringRight J (DerivedCategory.Plus (ModuleCat.{u} R))
          (ModuleCat.{u} R)).obj
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0)) ≪≫
        derivedSectionsZeroFunctorIso =
      Functor.isoWhiskerLeft toRestrictionFunctor
          EtalePullback.CoefficientDiagram.derivedSectionsZeroFunctorIso ≪≫
        toRestrictionSectionsFunctorIso := by
  apply Iso.ext
  apply NatTrans.ext
  funext D
  exact congrArg Iso.hom (toRestrictionDerivedSectionsIso_zero D)

end Langlands.Geometry.EtaleGeometricDiagram.CoefficientDiagram
