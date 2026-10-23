import Langlands.Geometry.EtaleEquivariantCoefficientDiagram
import Langlands.Geometry.EtaleCohomologyReindex

/-!
# Reindexing equivariant coefficients over varying schemes
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u v w t v' w' v'' w''

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type u} [CommRing R]
variable {J : Type v} [Category.{w} J] {S : J ⥤ Scheme.{u}ᵒᵖ}
variable [∀ {i j : J} (a : i ⟶ j), Etale (S.map a).unop]
variable {G : Type t} [Group G] {ρ : ∀ i, G →* (Aut (S.obj i).unop)ᵐᵒᵖ}
variable {hρ : ∀ {i j : J} (a : i ⟶ j) (g : G),
  (S.map a).unop ≫ (aut (ρ i) g).hom = (aut (ρ j) g).hom ≫ (S.map a).unop}
variable {K : Type v'} [Category.{w'} K] (F : K ⥤ J)

namespace EquivariantCoefficientDiagram

/-- Restrict the equivariant sheaves and their transition maps along an index functor. -/
def reindex (D : EquivariantCoefficientDiagram R S ρ hρ) :
    EquivariantCoefficientDiagram R (F ⋙ S) (fun i => ρ (F.obj i))
      (fun a g => hρ (F.map a) g) where
  obj i := D.obj (F.obj i)
  map a := D.map (F.map a)
  map_id i := by
    apply TranslationAction.Equivariant.Hom.ext
    simpa only [equivariantDiagramRestrictionId_hom_app_hom,
      CoefficientDiagram.reindex, forget] using
      (CoefficientDiagram.reindex F D.forget).map_id i
  map_comp a b := by
    apply TranslationAction.Equivariant.Hom.ext
    simpa only [TranslationAction.Equivariant.comp_hom,
      equivariantDiagramRestrictionComp_hom_app_hom, equivariantPullback_map_hom,
      CoefficientDiagram.reindex, forget] using
      (CoefficientDiagram.reindex F D.forget).map_comp a b

/-- Reindex an equivariant coefficient morphism by its components. -/
def reindexMap {D E : EquivariantCoefficientDiagram R S ρ hρ} (α : D ⟶ E) :
    reindex F D ⟶ reindex F E where
  app i := α.app (F.obj i)
  comm a := α.comm (F.map a)

/-- Reindexing is a functor on compatible equivariant coefficients. -/
def reindexFunctor :
    EquivariantCoefficientDiagram R S ρ hρ ⥤
      EquivariantCoefficientDiagram R (F ⋙ S) (fun i => ρ (F.obj i))
        (fun a g => hρ (F.map a) g) where
  obj := reindex F
  map := reindexMap F
  map_id D := by apply Hom.ext; rfl
  map_comp α β := by apply Hom.ext; rfl

/-- The underlying ordinary coefficient diagram is the published ordinary reindexing. -/
theorem reindex_forget (D : EquivariantCoefficientDiagram R S ρ hρ) :
    (reindex F D).forget = CoefficientDiagram.reindex F D.forget := rfl

/-- Forgetting equivariance commutes naturally with reindexing. -/
def reindexForgetFunctorIso :
    reindexFunctor (R := R) (S := S) (ρ := ρ) (hρ := hρ) F ⋙ forgetFunctor ≅
      forgetFunctor ⋙ CoefficientDiagram.reindexFunctor F :=
  Iso.refl _

/-- Evaluation after reindexing is evaluation at the image vertex. -/
def reindexEvaluationIso (i : K) :
    reindexFunctor (R := R) (S := S) (ρ := ρ) (hρ := hρ) F ⋙ evaluation i ≅
      evaluation (F.obj i) :=
  Iso.refl _

/-- Cohomology action diagrams reindex by precomposition. -/
theorem reindex_cohomology (D : EquivariantCoefficientDiagram R S ρ hρ) (q : ℕ) :
    (reindex F D).cohomology q = F ⋙ D.cohomology q := rfl

/-- Ordinary section action diagrams reindex by precomposition. -/
theorem reindex_sections (D : EquivariantCoefficientDiagram R S ρ hρ) :
    (reindex F D).sections = F ⋙ D.sections := rfl

/-- The cohomology comparison is natural in equivariant coefficient diagrams. -/
def reindexCohomologyFunctorIso (q : ℕ) :
    reindexFunctor (R := R) (S := S) (ρ := ρ) (hρ := hρ) F ⋙ cohomologyFunctor q ≅
      cohomologyFunctor q ⋙
        (CategoryTheory.Functor.whiskeringLeft K J (Action (ModuleCat.{u} R) G)).obj F :=
  Iso.refl _

/-- The section comparison is natural in equivariant coefficient diagrams. -/
def reindexSectionsFunctorIso :
    reindexFunctor (R := R) (S := S) (ρ := ρ) (hρ := hρ) F ⋙ sectionsFunctor ≅
      sectionsFunctor ⋙
        (CategoryTheory.Functor.whiskeringLeft K J (Action (ModuleCat.{u} R) G)).obj F :=
  Iso.refl _

/-- Reindexing preserves the canonical degree-zero comparison at every vertex. -/
theorem reindex_cohomologyZeroIso_hom_app
    (D : EquivariantCoefficientDiagram R S ρ hρ) (i : K) :
    (cohomologyZeroIso (reindex F D)).hom.app i =
      (cohomologyZeroIso D).hom.app (F.obj i) := rfl

/-- Reindexing preserves the inverse canonical comparison at every vertex. -/
theorem reindex_cohomologyZeroIso_inv_app
    (D : EquivariantCoefficientDiagram R S ρ hρ) (i : K) :
    (cohomologyZeroIso (reindex F D)).inv.app i =
      (cohomologyZeroIso D).inv.app (F.obj i) := rfl

/-- Identity reindexing is naturally the identity on equivariant coefficients. -/
def reindexIdIso :
    reindexFunctor (R := R) (S := S) (ρ := ρ) (hρ := hρ) (𝟭 J) ≅
      𝟭 (EquivariantCoefficientDiagram R S ρ hρ) :=
  Iso.refl _

variable {L : Type v''} [Category.{w''} L] (H : L ⥤ K)

/-- Successive reindexing is naturally reindexing along the composite index functor. -/
def reindexCompIso :
    reindexFunctor (R := R) (S := S) (ρ := ρ) (hρ := hρ) F ⋙ reindexFunctor H ≅
      reindexFunctor (H ⋙ F) :=
  Iso.refl _

end EquivariantCoefficientDiagram

end Langlands.Geometry.EtaleCohomologyAction
