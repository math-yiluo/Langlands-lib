import Langlands.Geometry.EtaleEquivariantPullbackCoherence

/-!
# Equivariant coefficients over varying schemes

Compatible equivariant sheaves on a supplied diagram of schemes induce
ordinary cohomology and section diagrams with geometric group actions.
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u v w t

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (R : Type u) [CommRing R]
variable {J : Type v} [Category.{w} J] (S : J ⥤ Scheme.{u}ᵒᵖ)
variable [∀ {i j : J} (a : i ⟶ j), Etale (S.map a).unop]
variable {G : Type t} [Group G] (ρ : ∀ i, G →* (Aut (S.obj i).unop)ᵐᵒᵖ)
variable (hρ : ∀ {i j : J} (a : i ⟶ j) (g : G),
  (S.map a).unop ≫ (aut (ρ i) g).hom = (aut (ρ j) g).hom ≫ (S.map a).unop)

/-- Equivariant restriction in the direction of a diagram arrow. -/
abbrev equivariantDiagramRestriction {i j : J} (a : i ⟶ j) :=
  equivariantPullback R (ρ i) (ρ j) (S.map a).unop (hρ a)

/-- Identity restriction, including the scheme diagram's identity equality. -/
def equivariantDiagramRestrictionId (i : J) :
    equivariantDiagramRestriction R S ρ hρ (𝟙 i) ≅ 𝟭 (EquivariantSheaf R (ρ i)) :=
  equivariantPullbackCongr R (ρ i) (ρ i) (hρ (𝟙 i)) (equivariantMap_id (ρ i))
      (congrArg Quiver.Hom.unop (S.map_id i)) ≪≫
    equivariantPullbackId R (ρ i)

/-- Composition restriction, including the scheme diagram's composition equality. -/
def equivariantDiagramRestrictionComp {i j k : J} (a : i ⟶ j) (b : j ⟶ k) :
    equivariantDiagramRestriction R S ρ hρ a ⋙
        equivariantDiagramRestriction R S ρ hρ b ≅
      equivariantDiagramRestriction R S ρ hρ (a ≫ b) :=
  equivariantPullbackComp R (ρ i) (ρ j) (ρ k) (S.map a).unop (S.map b).unop
      (hρ a) (hρ b) ≪≫
    equivariantPullbackCongr R (ρ i) (ρ k)
      (equivariantMap_comp (ρ i) (ρ j) (ρ k) (S.map a).unop (S.map b).unop
        (hρ a) (hρ b)) (hρ (a ≫ b))
      (congrArg Quiver.Hom.unop (S.map_comp a b)).symm

/-- The equivariant identity comparison has the existing ordinary comparison underneath. -/
@[simp] theorem equivariantDiagramRestrictionId_hom_app_hom (i : J)
    (F : EquivariantSheaf R (ρ i)) :
    ((equivariantDiagramRestrictionId R S ρ hρ i).hom.app F).hom =
      (diagramRestrictionId R S i).hom.app F.obj := by
  simp [equivariantDiagramRestrictionId, diagramRestrictionId]

/-- The equivariant composition comparison has the ordinary comparison underneath. -/
@[simp] theorem equivariantDiagramRestrictionComp_hom_app_hom
    {i j k : J} (a : i ⟶ j) (b : j ⟶ k) (F : EquivariantSheaf R (ρ i)) :
    ((equivariantDiagramRestrictionComp R S ρ hρ a b).hom.app F).hom =
      (diagramRestrictionComp R S a b).hom.app F.obj := by
  simp [equivariantDiagramRestrictionComp, diagramRestrictionComp]

/-- Actual equivariant sheaves with compatible transition maps.
Only sheaf-level data and laws are supplied; cohomological functoriality is derived. -/
structure EquivariantCoefficientDiagram where
  obj (i : J) : EquivariantSheaf R (ρ i)
  map {i j : J} (a : i ⟶ j) :
    (equivariantDiagramRestriction R S ρ hρ a).obj (obj i) ⟶ obj j
  map_id (i : J) : map (𝟙 i) = (equivariantDiagramRestrictionId R S ρ hρ i).hom.app (obj i)
  map_comp {i j k : J} (a : i ⟶ j) (b : j ⟶ k) :
    (equivariantDiagramRestrictionComp R S ρ hρ a b).hom.app (obj i) ≫ map (a ≫ b) =
      (equivariantDiagramRestriction R S ρ hρ b).map (map a) ≫ map b

namespace EquivariantCoefficientDiagram

variable {R S ρ hρ}

/-- Forgetting the actions retains the actual compatible ordinary coefficient sheaves. -/
def forget (D : EquivariantCoefficientDiagram R S ρ hρ) : CoefficientDiagram R S where
  obj i := (D.obj i).obj
  map a := (D.map a).hom
  map_id i := by
    simpa only [equivariantDiagramRestrictionId_hom_app_hom] using
      congrArg TranslationAction.Equivariant.Hom.hom (D.map_id i)
  map_comp a b := by
    simpa only [TranslationAction.Equivariant.comp_hom,
      equivariantDiagramRestrictionComp_hom_app_hom, equivariantPullback_map_hom] using
      congrArg TranslationAction.Equivariant.Hom.hom (D.map_comp a b)

/-- Pointwise equivariant sheaf maps compatible with diagram transitions. -/
@[ext] structure Hom (D E : EquivariantCoefficientDiagram R S ρ hρ) where
  app (i : J) : D.obj i ⟶ E.obj i
  comm {i j : J} (a : i ⟶ j) :
    D.map a ≫ app j = (equivariantDiagramRestriction R S ρ hρ a).map (app i) ≫ E.map a

def Hom.id (D : EquivariantCoefficientDiagram R S ρ hρ) : Hom D D where
  app i := 𝟙 (D.obj i)
  comm a := by simp

def Hom.comp {D E F : EquivariantCoefficientDiagram R S ρ hρ}
    (α : Hom D E) (β : Hom E F) : Hom D F where
  app i := α.app i ≫ β.app i
  comm a := by
    rw [← Category.assoc, α.comm, Category.assoc, β.comm]
    simp only [Functor.map_comp, Category.assoc]

instance : Category (EquivariantCoefficientDiagram R S ρ hρ) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp α := by ext i; simp [Hom.id, Hom.comp]
  comp_id α := by ext i; simp [Hom.id, Hom.comp]
  assoc α β γ := by ext i; simp [Hom.comp, Category.assoc]

@[simp] theorem id_app (D : EquivariantCoefficientDiagram R S ρ hρ) (i : J) :
    (𝟙 D : D ⟶ D).app i = 𝟙 (D.obj i) := rfl

@[simp] theorem comp_app {D E F : EquivariantCoefficientDiagram R S ρ hρ}
    (α : D ⟶ E) (β : E ⟶ F) (i : J) :
    (α ≫ β).app i = α.app i ≫ β.app i := rfl

/-- The faithful functor forgetting all group actions. -/
def forgetFunctor :
    EquivariantCoefficientDiagram R S ρ hρ ⥤ CoefficientDiagram R S where
  obj := forget
  map α :=
    { app := fun i => (α.app i).hom
      comm a := by
        exact congrArg TranslationAction.Equivariant.Hom.hom (α.comm a) }

instance : (forgetFunctor (R := R) (S := S) (ρ := ρ) (hρ := hρ)).Faithful where
  map_injective h := by
    apply Hom.ext
    funext i
    apply TranslationAction.Equivariant.Hom.ext
    exact congrArg (fun α => α.app i) h

/-- Evaluation retains the equivariant sheaf at a vertex. -/
def evaluation (i : J) :
    EquivariantCoefficientDiagram R S ρ hρ ⥤ EquivariantSheaf R (ρ i) where
  obj D := D.obj i
  map α := α.app i

/-- Ordinary cohomology, with its geometric group action, over the scheme diagram. -/
def cohomology (D : EquivariantCoefficientDiagram R S ρ hρ) (q : ℕ) :
    J ⥤ Action (ModuleCat.{u} R) G where
  obj i := (pullbackCohomologyFunctor R (ρ i) q).obj (D.obj i)
  map {i j} a :=
    (equivariantPullbackCohomology R (ρ i) (ρ j) (S.map a).unop (hρ a) q).app (D.obj i) ≫
      (pullbackCohomologyFunctor R (ρ j) q).map (D.map a)
  map_id i := by
    apply Action.Hom.ext
    simp only [Action.comp_hom, equivariantPullbackCohomology_app_hom,
      pullbackCohomologyFunctor_map_hom, Action.id_hom]
    change (D.forget.cohomology q).map (𝟙 i) = 𝟙 _
    exact (D.forget.cohomology q).map_id i
  map_comp a b := by
    apply Action.Hom.ext
    simpa only [Action.comp_hom, equivariantPullbackCohomology_app_hom,
      pullbackCohomologyFunctor_map_hom,
      CoefficientDiagram.cohomology, cohomologyMapWithCoefficients, forget] using
      (D.forget.cohomology q).map_comp a b

/-- The underlying transition is exactly the published ordinary cohomology transition. -/
@[simp] theorem cohomology_map_hom (D : EquivariantCoefficientDiagram R S ρ hρ)
    (q : ℕ) {i j : J} (a : i ⟶ j) :
    ((D.cohomology q).map a).hom = (D.forget.cohomology q).map a := by
  simp only [cohomology, Action.comp_hom, equivariantPullbackCohomology_app_hom,
    pullbackCohomologyFunctor_map_hom]
  rfl

/-- Coefficient morphisms induce natural equivariant maps of cohomology diagrams. -/
def cohomologyMap {D E : EquivariantCoefficientDiagram R S ρ hρ}
    (α : D ⟶ E) (q : ℕ) : D.cohomology q ⟶ E.cohomology q where
  app i := (pullbackCohomologyFunctor R (ρ i) q).map (α.app i)
  naturality {i j} a := by
    apply Action.Hom.ext
    simpa only [Action.comp_hom, cohomology_map_hom, pullbackCohomologyFunctor_map_hom,
      CoefficientDiagram.cohomologyMap, forgetFunctor, Functor.comp_map] using
      (CoefficientDiagram.cohomologyMap (forgetFunctor.map α) q).naturality a

/-- Cohomology action diagrams depend functorially on the equivariant coefficients. -/
def cohomologyFunctor (q : ℕ) :
    EquivariantCoefficientDiagram R S ρ hρ ⥤ (J ⥤ Action (ModuleCat.{u} R) G) where
  obj D := D.cohomology q
  map α := cohomologyMap α q
  map_id D := by
    apply NatTrans.ext
    funext i
    exact (pullbackCohomologyFunctor R (ρ i) q).map_id (D.obj i)
  map_comp α β := by
    apply NatTrans.ext
    funext i
    exact (pullbackCohomologyFunctor R (ρ i) q).map_comp (α.app i) (β.app i)

/-- Ordinary sections, with their geometric group action and restriction transitions. -/
def sections (D : EquivariantCoefficientDiagram R S ρ hρ) :
    J ⥤ Action (ModuleCat.{u} R) G where
  obj i := (pullbackSectionsFunctor R (ρ i)).obj (D.obj i)
  map {i j} a :=
    (equivariantPullbackSections R (ρ i) (ρ j) (S.map a).unop (hρ a)).app (D.obj i) ≫
      (pullbackSectionsFunctor R (ρ j)).map (D.map a)
  map_id i := by
    apply Action.Hom.ext
    simp only [Action.comp_hom, equivariantPullbackSections_app_hom,
      pullbackSectionsFunctor_map_hom, Action.id_hom]
    have h := D.forget.sections.map_id i
    rw [CoefficientDiagram.sections_map] at h
    exact h
  map_comp a b := by
    apply Action.Hom.ext
    simp only [Action.comp_hom, equivariantPullbackSections_app_hom,
      pullbackSectionsFunctor_map_hom]
    have h := D.forget.sections.map_comp a b
    simp only [CoefficientDiagram.sections_map] at h
    exact h

/-- Forgetting the actions gives the existing ordinary section transition. -/
@[simp] theorem sections_map_hom (D : EquivariantCoefficientDiagram R S ρ hρ)
    {i j : J} (a : i ⟶ j) :
    (D.sections.map a).hom = D.forget.sections.map a := by
  simp only [sections, Action.comp_hom, equivariantPullbackSections_app_hom,
    pullbackSectionsFunctor_map_hom, CoefficientDiagram.sections_map]
  rfl

/-- Coefficient morphisms induce natural equivariant maps of section diagrams. -/
def sectionsMap {D E : EquivariantCoefficientDiagram R S ρ hρ}
    (α : D ⟶ E) : D.sections ⟶ E.sections where
  app i := (pullbackSectionsFunctor R (ρ i)).map (α.app i)
  naturality {i j} a := by
    apply Action.Hom.ext
    have h := (CoefficientDiagram.sectionsFunctor.map (forgetFunctor.map α)).naturality a
    simp only [CoefficientDiagram.sectionsFunctor_map_app] at h
    dsimp only [CoefficientDiagram.sectionsFunctor, forgetFunctor] at h
    simpa only [Action.comp_hom, sections_map_hom, pullbackSectionsFunctor_map_hom,
      forgetFunctor] using h

/-- Section action diagrams depend functorially on equivariant coefficients. -/
def sectionsFunctor :
    EquivariantCoefficientDiagram R S ρ hρ ⥤ (J ⥤ Action (ModuleCat.{u} R) G) where
  obj D := D.sections
  map α := sectionsMap α
  map_id D := by
    apply NatTrans.ext
    funext i
    exact (pullbackSectionsFunctor R (ρ i)).map_id (D.obj i)
  map_comp α β := by
    apply NatTrans.ext
    funext i
    exact (pullbackSectionsFunctor R (ρ i)).map_comp (α.app i) (β.app i)

/-- The canonical degree-zero comparison is equivariant and natural along diagram arrows. -/
def cohomologyZeroIso (D : EquivariantCoefficientDiagram R S ρ hρ) :
    D.cohomology 0 ≅ D.sections :=
  NatIso.ofComponents
    (fun i => (pullbackCohomologyZeroFunctorIso R (ρ i)).app (D.obj i))
    (fun {i j} a => by
      dsimp only [cohomology, sections, Iso.app_hom]
      rw [Category.assoc, (pullbackCohomologyZeroFunctorIso R (ρ j)).hom.naturality,
        ← Category.assoc, equivariantPullbackCohomology_zero, Category.assoc])

/-- Degree-zero cohomology and sections agree naturally in the coefficient diagram. -/
def cohomologyZeroFunctorIso :
    cohomologyFunctor (R := R) (S := S) (ρ := ρ) (hρ := hρ) 0 ≅ sectionsFunctor :=
  NatIso.ofComponents cohomologyZeroIso (fun {D E} α => by
    apply NatTrans.ext
    funext i
    exact (pullbackCohomologyZeroFunctorIso R (ρ i)).hom.naturality (α.app i))

end EquivariantCoefficientDiagram

end Langlands.Geometry.EtaleCohomologyAction
