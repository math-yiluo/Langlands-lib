import Langlands.Geometry.EtaleEquivariantScalarExtensionPullback
import Langlands.Geometry.EtaleEquivariantCoefficientDiagram

/-!
# Scalar extension of compatible equivariant coefficients
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u v w t

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)

section GeometricComparisons

variable {X Y Z : Scheme.{u}} {G : Type t} [Group G]
variable (ρ : G →* (Aut X)ᵐᵒᵖ) (τ : G →* (Aut Y)ᵐᵒᵖ)

/-- The extension comparison respects equality transport of the geometric map. -/
theorem scalarExtensionEquivariantPullbackIso_congr
    {f k : Y ⟶ X} [Etale f] [Etale k]
    (hf : ∀ g, f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f)
    (hk : ∀ g, k ≫ (aut ρ g).hom = (aut τ g).hom ≫ k)
    (h : f = k) (F : EquivariantSheaf R ρ) :
    (scalarExtensionEquivariantPullbackIso φ ρ τ f hf).hom.app F ≫
        (scalarExtensionFunctor φ τ).map
          ((equivariantPullbackCongr R ρ τ hf hk h).hom.app F) =
      (equivariantPullbackCongr A ρ τ hf hk h).hom.app
          ((scalarExtensionFunctor φ ρ).obj F) ≫
        (scalarExtensionEquivariantPullbackIso φ ρ τ k hk).hom.app F := by
  subst k
  simp [equivariantPullbackCongr]

variable (υ : G →* (Aut Z)ᵐᵒᵖ) (f : Y ⟶ X) [Etale f] (k : Z ⟶ Y) [Etale k]
variable (hf : ∀ g, f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f)
variable (hk : ∀ g, k ≫ (aut τ g).hom = (aut υ g).hom ≫ k)

/-- Forward form of the geometric composition law for scalar extension. -/
theorem scalarExtensionEquivariantPullbackIso_comp_hom (F : EquivariantSheaf R ρ) :
    (equivariantPullbackComp A ρ τ υ f k hf hk).hom.app
        ((scalarExtensionFunctor φ ρ).obj F) ≫
      (scalarExtensionEquivariantPullbackIso φ ρ υ (k ≫ f)
        (equivariantMap_comp ρ τ υ f k hf hk)).hom.app F =
    (equivariantPullback A τ υ k hk).map
        ((scalarExtensionEquivariantPullbackIso φ ρ τ f hf).hom.app F) ≫
      (scalarExtensionEquivariantPullbackIso φ τ υ k hk).hom.app
        ((equivariantPullback R ρ τ f hf).obj F) ≫
      (scalarExtensionFunctor φ υ).map
        ((equivariantPullbackComp R ρ τ υ f k hf hk).hom.app F) := by
  apply (cancel_mono ((scalarExtensionFunctor φ υ).map
    ((equivariantPullbackComp R ρ τ υ f k hf hk).inv.app F))).1
  rw [Category.assoc, scalarExtensionEquivariantPullbackIso_comp]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    Iso.hom_inv_id_app_assoc]
  erw [(scalarExtensionFunctor φ υ).map_id]
  rfl

end GeometricComparisons

variable {J : Type v} [Category.{w} J] {S : J ⥤ Scheme.{u}ᵒᵖ}
variable [∀ {i j : J} (a : i ⟶ j), Etale (S.map a).unop]
variable {G : Type t} [Group G] {ρ : ∀ i, G →* (Aut (S.obj i).unop)ᵐᵒᵖ}
variable {hρ : ∀ {i j : J} (a : i ⟶ j) (g : G),
  (S.map a).unop ≫ (aut (ρ i) g).hom = (aut (ρ j) g).hom ≫ (S.map a).unop}

/-- Extension respects the diagram identity comparison, including equality transport. -/
theorem scalarExtension_diagramRestrictionId (i : J) (F : EquivariantSheaf R (ρ i)) :
    (scalarExtensionEquivariantPullbackIso φ (ρ i) (ρ i)
        (S.map (𝟙 i)).unop (hρ (𝟙 i))).hom.app F ≫
      (scalarExtensionFunctor φ (ρ i)).map
        ((equivariantDiagramRestrictionId R S ρ hρ i).hom.app F) =
    (equivariantDiagramRestrictionId A S ρ hρ i).hom.app
      ((scalarExtensionFunctor φ (ρ i)).obj F) := by
  dsimp only [equivariantDiagramRestrictionId, Iso.trans_hom, NatTrans.comp_app]
  rw [Functor.map_comp, ← Category.assoc, scalarExtensionEquivariantPullbackIso_congr,
    Category.assoc, scalarExtensionEquivariantPullbackIso_id]

/-- Extension respects the diagram composition comparison and its equality transport. -/
theorem scalarExtension_diagramRestrictionComp {i j k : J} (a : i ⟶ j) (b : j ⟶ k)
    (F : EquivariantSheaf R (ρ i)) :
    (equivariantDiagramRestrictionComp A S ρ hρ a b).hom.app
        ((scalarExtensionFunctor φ (ρ i)).obj F) ≫
      (scalarExtensionEquivariantPullbackIso φ (ρ i) (ρ k)
        (S.map (a ≫ b)).unop (hρ (a ≫ b))).hom.app F =
    (equivariantDiagramRestriction A S ρ hρ b).map
        ((scalarExtensionEquivariantPullbackIso φ (ρ i) (ρ j)
          (S.map a).unop (hρ a)).hom.app F) ≫
      (scalarExtensionEquivariantPullbackIso φ (ρ j) (ρ k)
        (S.map b).unop (hρ b)).hom.app
          ((equivariantDiagramRestriction R S ρ hρ a).obj F) ≫
      (scalarExtensionFunctor φ (ρ k)).map
        ((equivariantDiagramRestrictionComp R S ρ hρ a b).hom.app F) := by
  dsimp only [equivariantDiagramRestrictionComp, Iso.trans_hom, NatTrans.comp_app]
  rw [Category.assoc, ← scalarExtensionEquivariantPullbackIso_congr,
    ← Category.assoc, scalarExtensionEquivariantPullbackIso_comp_hom]
  simp only [Functor.map_comp, Category.assoc]

namespace EquivariantCoefficientDiagram

/-- Extend every coefficient sheaf and use the geometric comparison for transitions. -/
def extendScalars (D : EquivariantCoefficientDiagram R S ρ hρ) :
    EquivariantCoefficientDiagram A S ρ hρ where
  obj i := (scalarExtensionFunctor φ (ρ i)).obj (D.obj i)
  map {i j} a :=
    (scalarExtensionEquivariantPullbackIso φ (ρ i) (ρ j)
        (S.map a).unop (hρ a)).hom.app (D.obj i) ≫
      (scalarExtensionFunctor φ (ρ j)).map (D.map a)
  map_id i := by
    rw [D.map_id, scalarExtension_diagramRestrictionId]
  map_comp {i j k} a b := by
    rw [← Category.assoc, scalarExtension_diagramRestrictionComp]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [D.map_comp, Functor.map_comp]
    rw [← Category.assoc
      ((scalarExtensionEquivariantPullbackIso φ (ρ j) (ρ k)
        (S.map b).unop (hρ b)).hom.app _)]
    erw [← (scalarExtensionEquivariantPullbackIso φ (ρ j) (ρ k)
      (S.map b).unop (hρ b)).hom.naturality (D.map a)]
    simp only [Functor.comp_map, Functor.map_comp, Category.assoc]

/-- The underlying transition uses the ordinary sheafified extension comparison. -/
@[simp] theorem extendScalars_map_hom
    (D : EquivariantCoefficientDiagram R S ρ hρ) {i j : J} (a : i ⟶ j) :
    ((extendScalars φ D).map a).hom =
      (sheafExtendScalarsPullbackIso φ (S.map a).unop).hom.app (D.obj i).obj ≫
        (sheafExtendScalars φ (S.obj j).unop).map (D.map a).hom := rfl

/-- Apply scalar extension to each component of a compatible coefficient morphism. -/
def extendScalarsMap {D E : EquivariantCoefficientDiagram R S ρ hρ} (α : D ⟶ E) :
    extendScalars φ D ⟶ extendScalars φ E where
  app i := (scalarExtensionFunctor φ (ρ i)).map (α.app i)
  comm {i j} a := by
    dsimp only [extendScalars]
    rw [Category.assoc, ← Functor.map_comp, α.comm, Functor.map_comp, ← Category.assoc]
    erw [← (scalarExtensionEquivariantPullbackIso φ (ρ i) (ρ j)
      (S.map a).unop (hρ a)).hom.naturality (α.app i)]
    simp only [Functor.comp_map, Category.assoc]

/-- Sheafified extension of scalars on compatible equivariant coefficient diagrams. -/
def extendScalarsFunctor :
    EquivariantCoefficientDiagram R S ρ hρ ⥤ EquivariantCoefficientDiagram A S ρ hρ where
  obj := extendScalars φ
  map := extendScalarsMap φ
  map_id D := by
    apply Hom.ext
    funext i
    exact (scalarExtensionFunctor φ (ρ i)).map_id (D.obj i)
  map_comp α β := by
    apply Hom.ext
    funext i
    exact (scalarExtensionFunctor φ (ρ i)).map_comp (α.app i) (β.app i)

/-- Evaluation commutes with coefficient scalar extension. -/
def extendScalarsEvaluationIso (i : J) :
    extendScalarsFunctor (S := S) (ρ := ρ) (hρ := hρ) φ ⋙ evaluation i ≅
      evaluation i ⋙ scalarExtensionFunctor φ (ρ i) :=
  Iso.refl _

end EquivariantCoefficientDiagram

end Langlands.Geometry.EtaleCohomologyAction
