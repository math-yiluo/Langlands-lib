import Langlands.Geometry.EtaleCohomologyDiagram

/-!
# Morphisms and cohomology of compatible coefficient diagrams
-/

noncomputable section

namespace Langlands.Geometry.EtalePullback

open CategoryTheory AlgebraicGeometry

universe u v w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type u} [CommRing R]
variable {J : Type v} [Category.{w} J] {S : J ⥤ Scheme.{u}ᵒᵖ}
variable [∀ {i j : J} (a : i ⟶ j), Etale (S.map a).unop]

namespace CoefficientDiagram

/-- Morphisms of actual coefficient sheaves compatible with all diagram arrows. -/
@[ext] structure Hom (D E : CoefficientDiagram R S) where
  app (i : J) : D.obj i ⟶ E.obj i
  comm {i j : J} (a : i ⟶ j) :
    D.map a ≫ app j = (diagramRestriction R S a).map (app i) ≫ E.map a

/-- The pointwise identity morphism of compatible coefficients. -/
def Hom.id (D : CoefficientDiagram R S) : Hom D D where
  app i := 𝟙 (D.obj i)
  comm a := by simp

/-- Pointwise composition preserves compatibility with restriction. -/
def Hom.comp {D E F : CoefficientDiagram R S} (α : Hom D E) (β : Hom E F) :
    Hom D F where
  app i := α.app i ≫ β.app i
  comm a := by
    rw [← Category.assoc, α.comm, Category.assoc, β.comm]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]

instance : Category (CoefficientDiagram R S) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp α := by ext i; simp [Hom.id, Hom.comp]
  comp_id α := by ext i; simp [Hom.id, Hom.comp]
  assoc α β γ := by ext i; simp [Hom.comp, Category.assoc]

@[simp] theorem id_app (D : CoefficientDiagram R S) (i : J) :
    (𝟙 D : D ⟶ D).app i = 𝟙 (D.obj i) := rfl

@[simp] theorem comp_app {D E F : CoefficientDiagram R S}
    (α : D ⟶ E) (β : E ⟶ F) (i : J) :
    (α ≫ β).app i = α.app i ≫ β.app i := rfl

/-- Evaluation at a vertex is a functor to its actual coefficient-sheaf category. -/
def evaluation (i : J) :
    CoefficientDiagram R S ⥤ EtaleDerivedSections.ModuleSheaf (S.obj i).unop R where
  obj D := D.obj i
  map α := α.app i

/-- Compatible coefficient morphisms induce natural maps of cohomology diagrams. -/
def cohomologyMap {D E : CoefficientDiagram R S} (α : D ⟶ E) (q : ℕ) :
    D.cohomology q ⟶ E.cohomology q where
  app i := (EtaleDerivedSections.cohomology (S.obj i).unop R q).map (α.app i)
  naturality {i j} a := by
    dsimp only [cohomology, cohomologyMapWithCoefficients]
    simp only [Category.assoc]
    rw [← CategoryTheory.Functor.map_comp, α.comm, CategoryTheory.Functor.map_comp]
    simpa only [Category.assoc, Functor.comp_map] using congrArg
      (fun t => t ≫ (EtaleDerivedSections.cohomology (S.obj j).unop R q).map (E.map a))
      ((EtalePullback.cohomologyMap (S.map a).unop R q).naturality (α.app i)).symm

/-- Cohomology in every degree is functorial in compatible coefficient diagrams. -/
def cohomologyFunctor (q : ℕ) :
    CoefficientDiagram R S ⥤ (J ⥤ ModuleCat.{u} R) where
  obj D := D.cohomology q
  map α := cohomologyMap α q
  map_id D := by
    apply NatTrans.ext
    funext i
    exact (EtaleDerivedSections.cohomology (S.obj i).unop R q).map_id (D.obj i)
  map_comp α β := by
    apply NatTrans.ext
    funext i
    exact (EtaleDerivedSections.cohomology (S.obj i).unop R q).map_comp (α.app i) (β.app i)

/-- The diagram of global sections, transported from degree-zero cohomology. -/
def sections (D : CoefficientDiagram R S) : J ⥤ ModuleCat.{u} R where
  obj i := (EtaleDerivedSections.sections (S.obj i).unop R).obj (D.obj i)
  map {i j} a :=
    (EtaleDerivedSections.cohomologyZeroIso (S.obj i).unop R).inv.app (D.obj i) ≫
      (D.cohomology 0).map a ≫
      (EtaleDerivedSections.cohomologyZeroIso (S.obj j).unop R).hom.app (D.obj j)
  map_id i := by
    rw [CategoryTheory.Functor.map_id]
    change (EtaleDerivedSections.cohomologyZeroIso (S.obj i).unop R).inv.app (D.obj i) ≫
      𝟙 _ ≫ (EtaleDerivedSections.cohomologyZeroIso (S.obj i).unop R).hom.app (D.obj i) = _
    simp
  map_comp a b := by simp [Category.assoc]

/-- On every arrow, the section diagram is ordinary section restriction
followed by the coefficient-sheaf morphism. -/
theorem sections_map (D : CoefficientDiagram R S) {i j : J} (a : i ⟶ j) :
    D.sections.map a =
      (sectionsMap (S.map a).unop R).app (D.obj i) ≫
        (EtaleDerivedSections.sections (S.obj j).unop R).map (D.map a) := by
  dsimp only [sections, cohomology, cohomologyMapWithCoefficients]
  simp only [Category.assoc]
  rw [(EtaleDerivedSections.cohomologyZeroIso (S.obj j).unop R).hom.naturality]
  rw [← Category.assoc ((EtalePullback.cohomologyMap (S.map a).unop R 0).app (D.obj i)),
    cohomologyMap_zero]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

/-- The degree-zero identification is natural in every scheme-diagram arrow. -/
def cohomologyZeroIso (D : CoefficientDiagram R S) : D.cohomology 0 ≅ D.sections :=
  NatIso.ofComponents
    (fun i => (EtaleDerivedSections.cohomologyZeroIso (S.obj i).unop R).app (D.obj i))
    (fun {i j} a => by
      dsimp only [sections, Iso.app_hom]
      simp only [← Category.assoc, Iso.hom_inv_id_app]
      erw [Category.id_comp])

/-- Global-section diagrams are functorial in compatible coefficient morphisms. -/
def sectionsFunctor : CoefficientDiagram R S ⥤ (J ⥤ ModuleCat.{u} R) where
  obj D := D.sections
  map {D E} α :=
    (cohomologyZeroIso D).inv ≫ (cohomologyFunctor 0).map α ≫ (cohomologyZeroIso E).hom
  map_id D := by
    rw [CategoryTheory.Functor.map_id]
    change (cohomologyZeroIso D).inv ≫ 𝟙 (D.cohomology 0) ≫ (cohomologyZeroIso D).hom = _
    simp
  map_comp α β := by simp [Category.assoc]

/-- On a coefficient morphism, the section functor acts by ordinary sections
at every vertex. -/
theorem sectionsFunctor_map_app {D E : CoefficientDiagram R S}
    (α : D ⟶ E) (i : J) :
    (sectionsFunctor.map α).app i =
      (EtaleDerivedSections.sections (S.obj i).unop R).map (α.app i) := by
  exact NatIso.naturality_1
    (EtaleDerivedSections.cohomologyZeroIso (S.obj i).unop R) (α.app i)

/-- Degree-zero cohomology and sections agree naturally also in the coefficients. -/
def cohomologyZeroFunctorIso : cohomologyFunctor (R := R) (S := S) 0 ≅ sectionsFunctor :=
  NatIso.ofComponents cohomologyZeroIso (fun {D E} α => by
    dsimp only [sectionsFunctor]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp])

end CoefficientDiagram

end Langlands.Geometry.EtalePullback
