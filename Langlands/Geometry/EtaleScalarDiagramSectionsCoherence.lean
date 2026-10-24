import Langlands.Geometry.EtaleScalarDiagramCoherence
import Langlands.Geometry.EtaleScalarSectionsCoherence

/-!
# Scalar coherence for canonical section diagrams
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u v w t

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable (φ : R →+* A) (ψ : A →+* B)
variable {J : Type v} [Category.{w} J] (G : Type t) [Group G]

/-- Scalar restriction of a diagram of modules with group actions. -/
def actionDiagramRestrictScalarsFunctor :
    (J ⥤ Action (ModuleCat.{u} A) G) ⥤ (J ⥤ Action (ModuleCat.{u} R) G) :=
  (Functor.whiskeringRight J (Action (ModuleCat.{u} A) G)
    (Action (ModuleCat.{u} R) G)).obj ((ModuleCat.restrictScalars.{u} φ).mapAction G)

/-- Identity scalar restriction on diagrams of module actions. -/
def actionDiagramRestrictScalarsIdIso :
    actionDiagramRestrictScalarsFunctor (J := J) (RingHom.id R) G ≅
      𝟭 (J ⥤ Action (ModuleCat.{u} R) G) :=
  NatIso.ofComponents
    (fun V => NatIso.ofComponents
      (fun i => (actionRestrictScalarsIdIso G).app (V.obj i))
      (fun {i j} a => (actionRestrictScalarsIdIso G).hom.naturality (V.map a)))
    (fun {V W} α => by
      apply NatTrans.ext
      funext i
      exact (actionRestrictScalarsIdIso G).hom.naturality (α.app i))

/-- Composite scalar restriction on diagrams of module actions. -/
def actionDiagramRestrictScalarsCompIso :
    actionDiagramRestrictScalarsFunctor (J := J) (ψ.comp φ) G ≅
      actionDiagramRestrictScalarsFunctor ψ G ⋙ actionDiagramRestrictScalarsFunctor φ G :=
  NatIso.ofComponents
    (fun V => NatIso.ofComponents
      (fun i => (actionRestrictScalarsCompIso φ ψ G).app (V.obj i))
      (fun {i j} a => (actionRestrictScalarsCompIso φ ψ G).hom.naturality (V.map a)))
    (fun {V W} α => by
      apply NatTrans.ext
      funext i
      exact (actionRestrictScalarsCompIso φ ψ G).hom.naturality (α.app i))

/-- The diagram identity comparison is the module-action comparison at each vertex. -/
@[simp] theorem actionDiagramRestrictScalarsIdIso_hom_app_app
    (V : J ⥤ Action (ModuleCat.{u} R) G) (i : J) :
    ((actionDiagramRestrictScalarsIdIso G).hom.app V).app i =
      (actionRestrictScalarsIdIso G).hom.app (V.obj i) := rfl

/-- The inverse diagram identity comparison is the inverse comparison at each vertex. -/
@[simp] theorem actionDiagramRestrictScalarsIdIso_inv_app_app
    (V : J ⥤ Action (ModuleCat.{u} R) G) (i : J) :
    ((actionDiagramRestrictScalarsIdIso G).inv.app V).app i =
      (actionRestrictScalarsIdIso G).inv.app (V.obj i) := rfl

/-- The diagram composition comparison is the module-action comparison at each vertex. -/
@[simp] theorem actionDiagramRestrictScalarsCompIso_hom_app_app
    (V : J ⥤ Action (ModuleCat.{u} B) G) (i : J) :
    ((actionDiagramRestrictScalarsCompIso φ ψ G).hom.app V).app i =
      (actionRestrictScalarsCompIso φ ψ G).hom.app (V.obj i) := rfl

/-- The inverse diagram composition comparison is the inverse comparison at each vertex. -/
@[simp] theorem actionDiagramRestrictScalarsCompIso_inv_app_app
    (V : J ⥤ Action (ModuleCat.{u} B) G) (i : J) :
    ((actionDiagramRestrictScalarsCompIso φ ψ G).inv.app V).app i =
      (actionRestrictScalarsCompIso φ ψ G).inv.app (V.obj i) := rfl

variable {G} {S : J ⥤ Scheme.{u}ᵒᵖ}
variable [∀ {i j : J} (a : i ⟶ j), Etale (S.map a).unop]
variable {ρ : ∀ i, G →* (Aut (S.obj i).unop)ᵐᵒᵖ}
variable {hρ : ∀ {i j : J} (a : i ⟶ j) (g : G),
  (S.map a).unop ≫ (aut (ρ i) g).hom = (aut (ρ j) g).hom ≫ (S.map a).unop}

namespace EquivariantCoefficientDiagram

/-- The canonical section diagram comparison respects identity scalar restriction. -/
theorem restrictScalarsSections_id (D : EquivariantCoefficientDiagram R S ρ hρ) :
    sectionsFunctor.map ((restrictScalarsIdIso).hom.app D) =
      (restrictScalarsSectionsIso (RingHom.id R) D).hom ≫
        (actionDiagramRestrictScalarsIdIso G).hom.app D.sections := by
  apply NatTrans.ext
  funext i
  exact scalarRestrictionSectionsFunctor_id (ρ i) (D.obj i)

/-- The canonical section diagram comparison respects composite scalar restriction. -/
theorem restrictScalarsSections_comp (D : EquivariantCoefficientDiagram B S ρ hρ) :
    sectionsFunctor.map ((restrictScalarsCompIso φ ψ).hom.app D) ≫
        (restrictScalarsSectionsIso φ (restrictScalars ψ D)).hom ≫
        (actionDiagramRestrictScalarsFunctor φ G).map
          (restrictScalarsSectionsIso ψ D).hom =
      (restrictScalarsSectionsIso (ψ.comp φ) D).hom ≫
        (actionDiagramRestrictScalarsCompIso φ ψ G).hom.app D.sections := by
  apply NatTrans.ext
  funext i
  exact scalarRestrictionSectionsFunctor_comp φ ψ (ρ i) (D.obj i)

end EquivariantCoefficientDiagram

end Langlands.Geometry.EtaleCohomologyAction
