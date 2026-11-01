import Langlands.Geometry.EtaleGeometricCoefficientDiagram
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Action.Basic

/-! # Geometric action diagrams with arbitrary level morphisms -/

noncomputable section

universe u v w t uC vC wS wR

namespace Langlands.Geometry.EtaleGeometricDiagram

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Prod

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Curry a product-index diagram and recover its bundled actions. The
product functor laws supply the action laws and equivariant level maps. -/
def actionDiagramFunctor (J : Type v) [Category.{w} J]
    (G : Type t) [Monoid G] (C : Type uC) [Category.{vC} C] :
    ((J × SingleObj G) ⥤ C) ⥤ (J ⥤ Action C G) :=
  Functor.curry ⋙
    (Functor.whiskeringRight J (SingleObj G ⥤ C) (Action C G)).obj
      (Action.functorCategoryEquivalence C G).inverse

namespace CoefficientDiagram

open EtaleDerivedSections EtaleDerivedGlobalPullback

variable {R : Type u} [CommRing R]
variable {J : Type v} [Category.{w} J] {G : Type t} [Group G]
variable {S : (J × SingleObj G) ⥤ Scheme.{u}ᵒᵖ}
variable [∀ x : J × SingleObj G,
  HasDerivedCategory.{wS} (ModuleSheaf (S.obj x).unop R)]
variable [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

/-- Actual derived sections with geometric group actions and equivariant
transitions along arbitrary scheme morphisms. -/
def derivedAction (D : CoefficientDiagram R S) :
    J ⥤ Action (DerivedCategory.Plus (ModuleCat.{u} R)) G :=
  (actionDiagramFunctor J G _).obj D.derivedSections

/-- The derived action diagrams are functorial in the actual coefficient
sheaves and their compatible morphisms. -/
def derivedActionFunctor :
    CoefficientDiagram R S ⥤ (J ⥤ Action (DerivedCategory.Plus (ModuleCat.{u} R)) G) :=
  derivedSectionsFunctor ⋙ actionDiagramFunctor J G _

/-- The underlying derived object is the actual derived global sections
of the supplied sheaf at the indicated level. -/
@[simp] theorem derivedAction_obj_V (D : CoefficientDiagram R S) (i : J) :
    (D.derivedAction.obj i).V =
      (EtaleDerivedSectionsPlus.derivedSections
        (S.obj (i, SingleObj.star G)).unop R).obj (D.obj (i, SingleObj.star G)) := rfl

/-- A group element acts by the actual geometric derived pullback and
the coefficient transition along its product-index arrow. -/
theorem derivedAction_obj_ρ (D : CoefficientDiagram R S) (i : J) (g : G) :
    (D.derivedAction.obj i).ρ g =
      sheafDerivedPullbackWithCoefficients (S.map (𝟙 i ×ₘ g)).unop R
        (D.map (𝟙 i ×ₘ g)) := rfl

/-- The level transition is geometric derived pullback followed by the
actual coefficient map; its equivariance is built into its type. -/
theorem derivedAction_map_hom (D : CoefficientDiagram R S)
    {i j : J} (a : i ⟶ j) :
    (D.derivedAction.map a).hom =
      sheafDerivedPullbackWithCoefficients
        (S.map (a ×ₘ 𝟙 (SingleObj.star G))).unop R
        (D.map (a ×ₘ 𝟙 (SingleObj.star G))) := rfl

/-- Equivariance of every actual derived level map follows from the
commuting arrows in the product index category. -/
theorem derivedAction_map_comm (D : CoefficientDiagram R S)
    {i j : J} (a : i ⟶ j) (g : G) :
    (D.derivedAction.obj i).ρ g ≫ (D.derivedAction.map a).hom =
      (D.derivedAction.map a).hom ≫ (D.derivedAction.obj j).ρ g :=
  (D.derivedAction.map a).comm g

/-- Coefficient morphisms act by actual derived global sections at every
level, as equivariant morphisms. -/
@[simp] theorem derivedActionFunctor_map_app_hom
    {D E : CoefficientDiagram R S} (α : D ⟶ E) (i : J) :
    (((derivedActionFunctor (R := R) (S := S)).map α).app i).hom =
      (EtaleDerivedSectionsPlus.derivedSections
        (S.obj (i, SingleObj.star G)).unop R).map (α.app (i, SingleObj.star G)) := rfl

/-- Ordinary geometric cohomology with the actions and level maps
induced by the actual product-index coefficient diagram. -/
def cohomologyAction (D : CoefficientDiagram R S) (q : ℕ) :
    J ⥤ Action (ModuleCat.{u} R) G :=
  (actionDiagramFunctor J G _).obj (D.cohomology q)

/-- Ordinary cohomology action diagrams are functorial in coefficients. -/
def cohomologyActionFunctor (q : ℕ) :
    CoefficientDiagram R S ⥤ (J ⥤ Action (ModuleCat.{u} R) G) :=
  cohomologyFunctor q ⋙ actionDiagramFunctor J G _

/-- The underlying ordinary cohomology object is the actual right-derived
global-section object at the given level. -/
@[simp] theorem cohomologyAction_obj_V (D : CoefficientDiagram R S) (q : ℕ) (i : J) :
    ((D.cohomologyAction q).obj i).V =
      (EtaleDerivedSections.cohomology
        (S.obj (i, SingleObj.star G)).unop R q).obj (D.obj (i, SingleObj.star G)) := rfl

/-- The ordinary cohomology action is actual geometric pullback with the
given coefficient transition. -/
theorem cohomologyAction_obj_ρ (D : CoefficientDiagram R S)
    (q : ℕ) (i : J) (g : G) :
    ((D.cohomologyAction q).obj i).ρ g =
      cohomologyPullbackWithCoefficients (S.map (𝟙 i ×ₘ g)).unop R q
        (D.map (𝟙 i ×ₘ g)) :=
  cohomology_map D q (𝟙 i ×ₘ g)

/-- The ordinary cohomology level map is actual geometric pullback with
the coefficient transition, even for a non-etale level morphism. -/
theorem cohomologyAction_map_hom (D : CoefficientDiagram R S)
    (q : ℕ) {i j : J} (a : i ⟶ j) :
    ((D.cohomologyAction q).map a).hom =
      cohomologyPullbackWithCoefficients
        (S.map (a ×ₘ 𝟙 (SingleObj.star G))).unop R q
        (D.map (a ×ₘ 𝟙 (SingleObj.star G))) :=
  cohomology_map D q (a ×ₘ 𝟙 (SingleObj.star G))

/-- Coefficient morphisms act by actual ordinary cohomology at each level. -/
@[simp] theorem cohomologyActionFunctor_map_app_hom
    (q : ℕ) {D E : CoefficientDiagram R S} (α : D ⟶ E) (i : J) :
    (((cohomologyActionFunctor (R := R) (S := S) q).map α).app i).hom =
      (EtaleDerivedSections.cohomology
        (S.obj (i, SingleObj.star G)).unop R q).map (α.app (i, SingleObj.star G)) := rfl

/-- Actual sections with the geometric actions and equivariant level maps. -/
def sectionsAction (D : CoefficientDiagram R S) :
    J ⥤ Action (ModuleCat.{u} R) G :=
  (actionDiagramFunctor J G _).obj D.sections

/-- Section action diagrams are functorial in compatible coefficients. -/
def sectionsActionFunctor :
    CoefficientDiagram R S ⥤ (J ⥤ Action (ModuleCat.{u} R) G) :=
  sectionsFunctor ⋙ actionDiagramFunctor J G _

/-- The underlying section object is actual global sections of the sheaf. -/
@[simp] theorem sectionsAction_obj_V (D : CoefficientDiagram R S) (i : J) :
    (D.sectionsAction.obj i).V =
      (EtaleDerivedSections.sections
        (S.obj (i, SingleObj.star G)).unop R).obj (D.obj (i, SingleObj.star G)) := rfl

/-- The section action uses actual geometric section pullback and the
coefficient map. -/
theorem sectionsAction_obj_ρ (D : CoefficientDiagram R S) (i : J) (g : G) :
    (D.sectionsAction.obj i).ρ g =
      sectionsPullbackWithCoefficients (S.map (𝟙 i ×ₘ g)).unop R
        (D.map (𝟙 i ×ₘ g)) :=
  sections_map D (𝟙 i ×ₘ g)

/-- The section level transition uses actual geometric section pullback. -/
theorem sectionsAction_map_hom (D : CoefficientDiagram R S)
    {i j : J} (a : i ⟶ j) :
    (D.sectionsAction.map a).hom =
      sectionsPullbackWithCoefficients
        (S.map (a ×ₘ 𝟙 (SingleObj.star G))).unop R
        (D.map (a ×ₘ 𝟙 (SingleObj.star G))) :=
  sections_map D (a ×ₘ 𝟙 (SingleObj.star G))

/-- Coefficient morphisms act by actual global sections at each level. -/
@[simp] theorem sectionsActionFunctor_map_app_hom
    {D E : CoefficientDiagram R S} (α : D ⟶ E) (i : J) :
    (((sectionsActionFunctor (R := R) (S := S)).map α).app i).hom =
      (EtaleDerivedSections.sections
        (S.obj (i, SingleObj.star G)).unop R).map (α.app (i, SingleObj.star G)) := rfl

/-- Canonical homology recovery is equivariant and natural along every
level map of the geometric coefficient diagram. -/
def derivedActionHomologyIso (D : CoefficientDiagram R S) (q : ℕ) :
    D.derivedAction ⋙
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).mapAction G ≅
      D.cohomologyAction q :=
  NatIso.ofComponents
    (fun i => Action.mkIso
      ((D.derivedSectionsHomologyIso q).app (i, SingleObj.star G))
      (fun g => (D.derivedSectionsHomologyIso q).hom.naturality (𝟙 i ×ₘ g)))
    (fun {i j} a => by
      apply Action.Hom.ext
      exact (D.derivedSectionsHomologyIso q).hom.naturality
        (a ×ₘ 𝟙 (SingleObj.star G)))

/-- The underlying homology comparison is the canonical vertex comparison. -/
@[simp] theorem derivedActionHomologyIso_hom_app_hom
    (D : CoefficientDiagram R S) (q : ℕ) (i : J) :
    ((D.derivedActionHomologyIso q).hom.app i).hom =
      (EtaleDerivedSectionsPlus.homologyNatIso
        (S.obj (i, SingleObj.star G)).unop R q).hom.app
          (D.obj (i, SingleObj.star G)) := rfl

/-- Equivariant homology recovery is natural in actual coefficient
morphisms, as well as in level maps. -/
def derivedActionHomologyFunctorIso (q : ℕ) :
    derivedActionFunctor (R := R) (S := S) ⋙
        (Functor.whiskeringRight J (Action (DerivedCategory.Plus (ModuleCat.{u} R)) G)
          (Action (ModuleCat.{u} R) G)).obj
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).mapAction G) ≅
      cohomologyActionFunctor q :=
  NatIso.ofComponents (fun D => D.derivedActionHomologyIso q)
    (fun {D E} α => by
      apply NatTrans.ext
      funext i
      apply Action.Hom.ext
      exact (EtaleDerivedSectionsPlus.homologyNatIso
        (S.obj (i, SingleObj.star G)).unop R q).hom.naturality
          (α.app (i, SingleObj.star G)))

/-- The canonical degree-zero comparison recovers the actual section
action diagram, equivariantly along every level morphism. -/
def derivedActionZeroIso (D : CoefficientDiagram R S) :
    D.derivedAction ⋙
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction G ≅
      D.sectionsAction :=
  NatIso.ofComponents
    (fun i => Action.mkIso
      (D.derivedSectionsZeroIso.app (i, SingleObj.star G))
      (fun g => D.derivedSectionsZeroIso.hom.naturality (𝟙 i ×ₘ g)))
    (fun {i j} a => by
      apply Action.Hom.ext
      exact D.derivedSectionsZeroIso.hom.naturality
        (a ×ₘ 𝟙 (SingleObj.star G)))

/-- The underlying degree-zero map is the canonical map to actual sections. -/
@[simp] theorem derivedActionZeroIso_hom_app_hom
    (D : CoefficientDiagram R S) (i : J) :
    (D.derivedActionZeroIso.hom.app i).hom =
      (EtaleDerivedSectionsPlus.homologyZeroIso
        (S.obj (i, SingleObj.star G)).unop R).hom.app
          (D.obj (i, SingleObj.star G)) := rfl

/-- The equivariant degree-zero recovery is natural in compatible
coefficient morphisms. -/
def derivedActionZeroFunctorIso :
    derivedActionFunctor (R := R) (S := S) ⋙
        (Functor.whiskeringRight J (Action (DerivedCategory.Plus (ModuleCat.{u} R)) G)
          (Action (ModuleCat.{u} R) G)).obj
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction G) ≅
      sectionsActionFunctor :=
  NatIso.ofComponents (fun D => D.derivedActionZeroIso)
    (fun {D E} α => by
      apply NatTrans.ext
      funext i
      apply Action.Hom.ext
      exact (EtaleDerivedSectionsPlus.homologyZeroIso
        (S.obj (i, SingleObj.star G)).unop R).hom.naturality
          (α.app (i, SingleObj.star G)))

/-- Ordinary degree-zero cohomology recovers actual sections, naturally
in coefficients and levels and with its geometric group action. -/
def cohomologyActionZeroFunctorIso :
    cohomologyActionFunctor (R := R) (S := S) 0 ≅ sectionsActionFunctor :=
  Functor.isoWhiskerRight cohomologyZeroFunctorIso (actionDiagramFunctor J G _)

end CoefficientDiagram

end Langlands.Geometry.EtaleGeometricDiagram
