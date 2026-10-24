import Langlands.Geometry.EtaleScalarDiagram
import Langlands.Geometry.EtaleScalarCoherence

/-!
# Scalar coherence for equivariant coefficient diagrams
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u v w t

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
variable (φ : R →+* A) (ψ : A →+* B) (χ : B →+* C)
variable {J : Type v} [Category.{w} J] {S : J ⥤ Scheme.{u}ᵒᵖ}
variable [∀ {i j : J} (a : i ⟶ j), Etale (S.map a).unop]
variable {G : Type t} [Group G] {ρ : ∀ i, G →* (Aut (S.obj i).unop)ᵐᵒᵖ}
variable {hρ : ∀ {i j : J} (a : i ⟶ j) (g : G),
  (S.map a).unop ≫ (aut (ρ i) g).hom = (aut (ρ j) g).hom ≫ (S.map a).unop}

namespace EquivariantCoefficientDiagram

/-- Identity scalar restriction is naturally the identity on coefficient diagrams. -/
def restrictScalarsIdIso :
    restrictScalarsFunctor (S := S) (ρ := ρ) (hρ := hρ) (RingHom.id R) ≅
      𝟭 (EquivariantCoefficientDiagram R S ρ hρ) :=
  NatIso.ofComponents
    (fun D =>
      { hom :=
          { app := fun i => (scalarRestrictionIdIso (ρ i)).hom.app (D.obj i)
            comm := fun a => by
              apply TranslationAction.Equivariant.Hom.ext
              simp only [TranslationAction.Equivariant.comp_hom,
                equivariantPullback_map_hom,
                scalarRestrictionIdIso_hom_app_hom]
              ext U x
              rfl }
        inv :=
          { app := fun i => (scalarRestrictionIdIso (ρ i)).inv.app (D.obj i)
            comm := fun a => by
              apply TranslationAction.Equivariant.Hom.ext
              simp only [TranslationAction.Equivariant.comp_hom,
                equivariantPullback_map_hom,
                scalarRestrictionIdIso_inv_app_hom]
              ext U x
              rfl }
        hom_inv_id := by
          apply Hom.ext
          funext i
          exact (scalarRestrictionIdIso (ρ i)).hom_inv_id_app (D.obj i)
        inv_hom_id := by
          apply Hom.ext
          funext i
          exact (scalarRestrictionIdIso (ρ i)).inv_hom_id_app (D.obj i) })
    (fun {D E} α => by
      apply Hom.ext
      funext i
      exact (scalarRestrictionIdIso (ρ i)).hom.naturality (α.app i))

/-- Composite scalar restriction is naturally successive restriction on diagrams. -/
def restrictScalarsCompIso :
    restrictScalarsFunctor (S := S) (ρ := ρ) (hρ := hρ) (ψ.comp φ) ≅
      restrictScalarsFunctor ψ ⋙ restrictScalarsFunctor φ :=
  NatIso.ofComponents
    (fun D =>
      { hom :=
          { app := fun i => (scalarRestrictionCompIso φ ψ (ρ i)).hom.app (D.obj i)
            comm := fun a => by
              apply TranslationAction.Equivariant.Hom.ext
              simp only [TranslationAction.Equivariant.comp_hom,
                equivariantPullback_map_hom,
                scalarRestrictionCompIso_hom_app_hom]
              ext U x
              rfl }
        inv :=
          { app := fun i => (scalarRestrictionCompIso φ ψ (ρ i)).inv.app (D.obj i)
            comm := fun a => by
              apply TranslationAction.Equivariant.Hom.ext
              simp only [TranslationAction.Equivariant.comp_hom,
                equivariantPullback_map_hom,
                scalarRestrictionCompIso_inv_app_hom]
              ext U x
              rfl }
        hom_inv_id := by
          apply Hom.ext
          funext i
          exact (scalarRestrictionCompIso φ ψ (ρ i)).hom_inv_id_app (D.obj i)
        inv_hom_id := by
          apply Hom.ext
          funext i
          exact (scalarRestrictionCompIso φ ψ (ρ i)).inv_hom_id_app (D.obj i) })
    (fun {D E} α => by
      apply Hom.ext
      funext i
      exact (scalarRestrictionCompIso φ ψ (ρ i)).hom.naturality (α.app i))

/-- Evaluation of the identity comparison gives the equivariant sheaf comparison. -/
@[simp] theorem restrictScalarsIdIso_hom_app_app
    (D : EquivariantCoefficientDiagram R S ρ hρ) (i : J) :
    ((restrictScalarsIdIso).hom.app D).app i =
      (scalarRestrictionIdIso (ρ i)).hom.app (D.obj i) := rfl

/-- Evaluation of the inverse identity comparison gives the inverse sheaf comparison. -/
@[simp] theorem restrictScalarsIdIso_inv_app_app
    (D : EquivariantCoefficientDiagram R S ρ hρ) (i : J) :
    ((restrictScalarsIdIso).inv.app D).app i =
      (scalarRestrictionIdIso (ρ i)).inv.app (D.obj i) := rfl

/-- Evaluation of the composition comparison gives the equivariant sheaf comparison. -/
@[simp] theorem restrictScalarsCompIso_hom_app_app
    (D : EquivariantCoefficientDiagram B S ρ hρ) (i : J) :
    ((restrictScalarsCompIso φ ψ).hom.app D).app i =
      (scalarRestrictionCompIso φ ψ (ρ i)).hom.app (D.obj i) := rfl

/-- Evaluation of the inverse composition comparison gives the inverse sheaf comparison. -/
@[simp] theorem restrictScalarsCompIso_inv_app_app
    (D : EquivariantCoefficientDiagram B S ρ hρ) (i : J) :
    ((restrictScalarsCompIso φ ψ).inv.app D).app i =
      (scalarRestrictionCompIso φ ψ (ρ i)).inv.app (D.obj i) := rfl

/-- Splitting and removing the identity at the source ring gives the identity diagram map. -/
theorem restrictScalarsCompIso_id_left (D : EquivariantCoefficientDiagram A S ρ hρ) :
    (restrictScalarsCompIso (RingHom.id R) φ).hom.app D ≫
        (restrictScalarsIdIso).hom.app (restrictScalars φ D) =
      𝟙 (restrictScalars φ D) := by
  apply Hom.ext
  funext i
  exact scalarRestrictionCompIso_id_left φ (ρ i) (D.obj i)

set_option maxHeartbeats 800000 in
/-- Splitting and removing the identity at the target ring gives the identity diagram map. -/
theorem restrictScalarsCompIso_id_right (D : EquivariantCoefficientDiagram A S ρ hρ) :
    (restrictScalarsCompIso φ (RingHom.id A)).hom.app D ≫
        (restrictScalarsFunctor φ).map ((restrictScalarsIdIso).hom.app D) =
      𝟙 (restrictScalars φ D) := by
  apply Hom.ext
  funext i
  exact scalarRestrictionCompIso_id_right φ (ρ i) (D.obj i)

set_option maxHeartbeats 800000 in
/-- The two splittings of a triple ring composite agree as coefficient diagram maps. -/
theorem restrictScalarsCompIso_assoc (D : EquivariantCoefficientDiagram C S ρ hρ) :
    (restrictScalarsCompIso φ (χ.comp ψ)).hom.app D ≫
        (restrictScalarsFunctor φ).map ((restrictScalarsCompIso ψ χ).hom.app D) =
      (restrictScalarsCompIso (ψ.comp φ) χ).hom.app D ≫
        (restrictScalarsCompIso φ ψ).hom.app (restrictScalars χ D) := by
  apply Hom.ext
  funext i
  exact scalarRestrictionCompIso_assoc φ ψ χ (ρ i) (D.obj i)

end EquivariantCoefficientDiagram

end Langlands.Geometry.EtaleCohomologyAction
