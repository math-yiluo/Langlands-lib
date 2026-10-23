import Langlands.Geometry.EtaleCohomologyDiagramFunctor

/-!
# Reindexing compatible coefficient and cohomology diagrams
-/

noncomputable section

namespace Langlands.Geometry.EtalePullback

open CategoryTheory AlgebraicGeometry

universe u v w v' w'

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type u} [CommRing R]
variable {J : Type v} [Category.{w} J] {S : J ⥤ Scheme.{u}ᵒᵖ}
variable [∀ {i j : J} (a : i ⟶ j), Etale (S.map a).unop]
variable {K : Type v'} [Category.{w'} K] (F : K ⥤ J)

instance {i j : K} (a : i ⟶ j) : Etale ((F ⋙ S).map a).unop :=
  inferInstanceAs (Etale (S.map (F.map a)).unop)

namespace CoefficientDiagram

/-- The coefficient identity law transported along an equality of index arrows. -/
theorem map_id_transport (D : CoefficientDiagram R S) {i : J}
    (a : i ⟶ i) (h : a = 𝟙 i) :
    D.map a = (restrictionCongr R
      (congrArg Quiver.Hom.unop ((congrArg S.map h).trans (S.map_id i))) ≪≫
        restrictionId (ModuleCat.{u} R)).hom.app (D.obj i) := by
  subst a
  exact D.map_id i

/-- The coefficient composition law transported along an equality of index arrows. -/
theorem map_comp_transport (D : CoefficientDiagram R S) {i j k : J}
    (a : i ⟶ j) (b : j ⟶ k) (c : i ⟶ k) (h : c = a ≫ b) :
    (restrictionComp (S.map a).unop (ModuleCat.{u} R) (S.map b).unop ≪≫
      restrictionCongr R
        (congrArg Quiver.Hom.unop ((congrArg S.map h).trans (S.map_comp a b))).symm
          ).hom.app (D.obj i) ≫ D.map c =
      (diagramRestriction R S b).map (D.map a) ≫ D.map b := by
  subst c
  exact D.map_comp a b

/-- Restrict compatible coefficient sheaves along an index functor. -/
def reindex (D : CoefficientDiagram R S) : CoefficientDiagram R (F ⋙ S) where
  obj i := D.obj (F.obj i)
  map a := D.map (F.map a)
  map_id i := D.map_id_transport (F.map (𝟙 i)) (F.map_id i)
  map_comp a b := D.map_comp_transport (F.map a) (F.map b) (F.map (a ≫ b)) (F.map_comp a b)

/-- Reindex a compatible coefficient morphism by its components. -/
def reindexMap {D E : CoefficientDiagram R S} (α : D ⟶ E) :
    reindex F D ⟶ reindex F E where
  app i := α.app (F.obj i)
  comm a := α.comm (F.map a)

/-- Reindexing is functorial in compatible coefficients. -/
def reindexFunctor : CoefficientDiagram R S ⥤ CoefficientDiagram R (F ⋙ S) where
  obj := reindex F
  map := reindexMap F
  map_id D := by apply Hom.ext; rfl
  map_comp α β := by apply Hom.ext; rfl

/-- Cohomology of reindexed coefficients is the precomposed cohomology diagram. -/
theorem reindex_cohomology (D : CoefficientDiagram R S) (q : ℕ) :
    (reindex F D).cohomology q = F ⋙ D.cohomology q := rfl

/-- Global sections of reindexed coefficients form the precomposed section diagram. -/
theorem reindex_sections (D : CoefficientDiagram R S) :
    (reindex F D).sections = F ⋙ D.sections := rfl

/-- The cohomology comparison is natural in the compatible coefficient diagram. -/
def reindexCohomologyFunctorIso (q : ℕ) :
    reindexFunctor (R := R) (S := S) F ⋙ cohomologyFunctor q ≅
      cohomologyFunctor q ⋙ (CategoryTheory.Functor.whiskeringLeft K J (ModuleCat.{u} R)).obj F :=
  Iso.refl _

/-- The global-section comparison is natural in compatible coefficients. -/
def reindexSectionsFunctorIso :
    reindexFunctor (R := R) (S := S) F ⋙ sectionsFunctor ≅
      sectionsFunctor ⋙ (CategoryTheory.Functor.whiskeringLeft K J (ModuleCat.{u} R)).obj F :=
  Iso.refl _

/-- Reindexing preserves the canonical comparison between degree zero and sections. -/
theorem reindex_cohomologyZeroIso_hom_app (D : CoefficientDiagram R S) (i : K) :
    (cohomologyZeroIso (reindex F D)).hom.app i =
      (cohomologyZeroIso D).hom.app (F.obj i) := rfl

end CoefficientDiagram

end Langlands.Geometry.EtalePullback
