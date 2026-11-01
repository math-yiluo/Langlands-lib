import Langlands.Geometry.EtaleCoefficientEquivalence
import Langlands.Geometry.EtaleDerivedDiagram

/-! # Comparison of cohomological diagrams under coefficient transport -/

noncomputable section

universe u v w wS wR

namespace Langlands.Geometry.EtaleGeometricDiagram.CoefficientDiagram

open CategoryTheory AlgebraicGeometry
open EtaleInverseImage EtaleDerivedSections EtaleDerivedGlobalPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type u} [CommRing R]
variable {J : Type v} [Category.{w} J] {S : J ⥤ Scheme.{u}ᵒᵖ}
variable [∀ {i j : J} (a : i ⟶ j), Etale (S.map a).unop]
variable [∀ i : J, HasDerivedCategory.{wS} (ModuleSheaf (S.obj i).unop R)]
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

/-- Transporting restriction coefficients leaves the actual derived-section
diagram canonically unchanged, with identity components. -/
def ofRestrictionDerivedSectionsIso (D : EtalePullback.CoefficientDiagram R S) :
    (ofRestriction D).derivedSections ≅ D.derivedSections :=
  NatIso.ofComponents (fun i => Iso.refl _)
    (fun {i j} a => by
      change sheafDerivedPullbackWithCoefficients (S.map a).unop R
        ((inverseImageIsoRestriction (S.map a).unop R).hom.app (D.obj i) ≫ D.map a) ≫
          𝟙 _ =
        𝟙 _ ≫ EtalePullback.derivedSectionsMapWithCoefficients (S.map a).unop R (D.map a)
      simpa only [Category.comp_id, Category.id_comp] using
        sheafDerivedPullbackWithCoefficients_restriction (S.map a).unop R (D.map a))

/-- Transporting coefficients commutes with derived-section diagram functors. -/
def ofRestrictionDerivedSectionsFunctorIso :
    ofRestrictionFunctor (R := R) (S := S) ⋙ derivedSectionsFunctor ≅
      EtalePullback.CoefficientDiagram.derivedSectionsFunctor :=
  NatIso.ofComponents ofRestrictionDerivedSectionsIso
    (fun {D E} α => by
      apply NatTrans.ext
      funext i
      change (EtaleDerivedSectionsPlus.derivedSections (S.obj i).unop R).map (α.app i) ≫
        𝟙 _ = 𝟙 _ ≫
          (EtaleDerivedSectionsPlus.derivedSections (S.obj i).unop R).map (α.app i)
      simp)

/-- Transporting restriction coefficients preserves ordinary cohomology
diagrams in each nonnegative degree, with identity components. -/
def ofRestrictionCohomologyIso (D : EtalePullback.CoefficientDiagram R S) (q : ℕ) :
    (ofRestriction D).cohomology q ≅ D.cohomology q :=
  NatIso.ofComponents (fun i => Iso.refl _)
    (fun {i j} a => by
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rw [cohomology_map]
      exact cohomologyPullbackWithCoefficients_restriction (S.map a).unop R q (D.map a))

/-- The ordinary-cohomology comparison is natural in compatible coefficients. -/
def ofRestrictionCohomologyFunctorIso (q : ℕ) :
    ofRestrictionFunctor (R := R) (S := S) ⋙ cohomologyFunctor q ≅
      EtalePullback.CoefficientDiagram.cohomologyFunctor q :=
  NatIso.ofComponents (fun D => ofRestrictionCohomologyIso D q)
    (fun {D E} α => by
      apply NatTrans.ext
      funext i
      change (EtaleDerivedSections.cohomology (S.obj i).unop R q).map (α.app i) ≫
        𝟙 _ = 𝟙 _ ≫
          (EtaleDerivedSections.cohomology (S.obj i).unop R q).map (α.app i)
      simp)

/-- Transporting restriction coefficients preserves actual section diagrams. -/
def ofRestrictionSectionsIso (D : EtalePullback.CoefficientDiagram R S) :
    (ofRestriction D).sections ≅ D.sections :=
  NatIso.ofComponents (fun i => Iso.refl _)
    (fun {i j} a => by
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rw [sections_map, EtalePullback.CoefficientDiagram.sections_map]
      simp only [sectionsPullbackWithCoefficients, ofRestriction,
        Functor.map_comp, ← Category.assoc, sectionsPullback_restriction])

/-- The section comparison is natural in compatible coefficients. -/
def ofRestrictionSectionsFunctorIso :
    ofRestrictionFunctor (R := R) (S := S) ⋙ sectionsFunctor ≅
      EtalePullback.CoefficientDiagram.sectionsFunctor :=
  NatIso.ofComponents ofRestrictionSectionsIso
    (fun {D E} α => by
      apply NatTrans.ext
      funext i
      change (EtaleDerivedSections.sections (S.obj i).unop R).map (α.app i) ≫ 𝟙 _ =
        𝟙 _ ≫ (EtalePullback.CoefficientDiagram.sectionsFunctor.map α).app i
      rw [EtalePullback.CoefficientDiagram.sectionsFunctor_map_app]
      simp)

end Langlands.Geometry.EtaleGeometricDiagram.CoefficientDiagram
