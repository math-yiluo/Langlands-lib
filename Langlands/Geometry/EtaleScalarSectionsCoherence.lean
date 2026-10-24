import Langlands.Geometry.EtaleScalarCoherence

/-!
# Scalar identity and composition on ordinary section actions
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u t

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable (φ : R →+* A) (ψ : A →+* B) (X : Scheme.{u})

/-- The canonical section comparison respects the scalar identity comparison. -/
theorem scalarRestrictionSections_id (F : EtaleDerivedSections.ModuleSheaf X R) :
    (EtaleDerivedSections.sections X R).map
        ((sheafRestrictScalarsIdIso X).hom.app F) =
      (scalarRestrictionSectionsIso (RingHom.id R) (X := X)).hom.app F ≫
        (ModuleCat.restrictScalarsId R).hom.app
          ((EtaleDerivedSections.sections X R).obj F) := by
  rw [← NatIso.naturality_2 (EtaleDerivedSections.sectionsIso X R)
    ((sheafRestrictScalarsIdIso X).hom.app F)]
  change
    (EtaleDerivedSections.sectionsIso X R).hom.app
        ((sheafRestrictScalars (RingHom.id R) X).obj F) ≫
      (ModuleCat.restrictScalarsId R).hom.app _ ≫
        (EtaleDerivedSections.sectionsIso X R).inv.app F =
      ((EtaleDerivedSections.sectionsIso X R).hom.app
        ((sheafRestrictScalars (RingHom.id R) X).obj F) ≫
          (ModuleCat.restrictScalars (RingHom.id R)).map
            ((EtaleDerivedSections.sectionsIso X R).inv.app F)) ≫
        (ModuleCat.restrictScalarsId R).hom.app _
  rw [Category.assoc, (ModuleCat.restrictScalarsId R).hom.naturality]
  rfl

/-- The canonical section comparison respects the scalar composition comparison. -/
theorem scalarRestrictionSections_comp (F : EtaleDerivedSections.ModuleSheaf X B) :
    (EtaleDerivedSections.sections X R).map
        ((sheafRestrictScalarsCompIso φ ψ X).hom.app F) ≫
        (scalarRestrictionSectionsIso φ (X := X)).hom.app
          ((sheafRestrictScalars ψ X).obj F) ≫
        (ModuleCat.restrictScalars φ).map
          ((scalarRestrictionSectionsIso ψ (X := X)).hom.app F) =
      (scalarRestrictionSectionsIso (ψ.comp φ) (X := X)).hom.app F ≫
        (ModuleCat.restrictScalarsComp φ ψ).hom.app
          ((EtaleDerivedSections.sections X B).obj F) := by
  rw [← NatIso.naturality_2 (EtaleDerivedSections.sectionsIso X R)
    ((sheafRestrictScalarsCompIso φ ψ X).hom.app F)]
  dsimp [scalarRestrictionSectionsIso]
  simp only [Functor.map_comp, Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [(ModuleCat.restrictScalars φ).map_id, Category.id_comp]

variable (G : Type t) [Group G]

/-- Identity scalar restriction on modules with an algebraic group action. -/
def actionRestrictScalarsIdIso :
    (ModuleCat.restrictScalars.{u} (RingHom.id R)).mapAction G ≅
      𝟭 (Action (ModuleCat.{u} R) G) :=
  Functor.mapActionCongr G (ModuleCat.restrictScalarsId R)

/-- Composite scalar restriction on modules with an algebraic group action. -/
def actionRestrictScalarsCompIso :
    (ModuleCat.restrictScalars.{u} (ψ.comp φ)).mapAction G ≅
      (ModuleCat.restrictScalars.{u} ψ).mapAction G ⋙
        (ModuleCat.restrictScalars.{u} φ).mapAction G :=
  Functor.mapActionCongr G (ModuleCat.restrictScalarsComp φ ψ) ≪≫
    Functor.mapActionComp G (ModuleCat.restrictScalars ψ) (ModuleCat.restrictScalars φ)

/-- Forgetting the action recovers the module identity comparison. -/
@[simp] theorem actionRestrictScalarsIdIso_hom_app_hom (V : Action (ModuleCat.{u} R) G) :
    ((actionRestrictScalarsIdIso G).hom.app V).hom =
      (ModuleCat.restrictScalarsId R).hom.app V.V := rfl

/-- Forgetting the action recovers the inverse module identity comparison. -/
@[simp] theorem actionRestrictScalarsIdIso_inv_app_hom (V : Action (ModuleCat.{u} R) G) :
    ((actionRestrictScalarsIdIso G).inv.app V).hom =
      (ModuleCat.restrictScalarsId R).inv.app V.V := rfl

/-- Forgetting the action recovers the module composition comparison. -/
@[simp] theorem actionRestrictScalarsCompIso_hom_app_hom (V : Action (ModuleCat.{u} B) G) :
    ((actionRestrictScalarsCompIso φ ψ G).hom.app V).hom =
      (ModuleCat.restrictScalarsComp φ ψ).hom.app V.V := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- Forgetting the action recovers the inverse module composition comparison. -/
@[simp] theorem actionRestrictScalarsCompIso_inv_app_hom (V : Action (ModuleCat.{u} B) G) :
    ((actionRestrictScalarsCompIso φ ψ G).inv.app V).hom =
      (ModuleCat.restrictScalarsComp φ ψ).inv.app V.V := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

variable {X G} (ρ : G →* (Aut X)ᵐᵒᵖ)

/-- The scalar identity comparison commutes with the canonical ordinary-section action comparison. -/
theorem scalarRestrictionSectionsFunctor_id (F : EquivariantSheaf R ρ) :
    (pullbackSectionsFunctor R ρ).map ((scalarRestrictionIdIso ρ).hom.app F) =
      (scalarRestrictionSectionsFunctorIso (RingHom.id R) ρ).hom.app F ≫
        (actionRestrictScalarsIdIso G).hom.app ((pullbackSectionsFunctor R ρ).obj F) := by
  apply Action.Hom.ext
  simp only [Action.comp_hom, pullbackSectionsFunctor_map_hom,
    scalarRestrictionIdIso_hom_app_hom]
  exact scalarRestrictionSections_id X F.obj

/-- The scalar composition comparison commutes with successive ordinary-section action comparisons. -/
theorem scalarRestrictionSectionsFunctor_comp (F : EquivariantSheaf B ρ) :
    (pullbackSectionsFunctor R ρ).map ((scalarRestrictionCompIso φ ψ ρ).hom.app F) ≫
        (scalarRestrictionSectionsFunctorIso φ ρ).hom.app
          ((scalarRestrictionFunctor ψ ρ).obj F) ≫
        ((ModuleCat.restrictScalars φ).mapAction G).map
          ((scalarRestrictionSectionsFunctorIso ψ ρ).hom.app F) =
      (scalarRestrictionSectionsFunctorIso (ψ.comp φ) ρ).hom.app F ≫
        (actionRestrictScalarsCompIso φ ψ G).hom.app
          ((pullbackSectionsFunctor B ρ).obj F) := by
  apply Action.Hom.ext
  simp only [Action.comp_hom, pullbackSectionsFunctor_map_hom,
    scalarRestrictionCompIso_hom_app_hom, Functor.mapAction_map_hom]
  change _ = (scalarRestrictionSectionsIso (ψ.comp φ) (X := X)).hom.app F.obj ≫
    (ModuleCat.restrictScalarsComp φ ψ).hom.app
      ((EtaleDerivedSections.sections X B).obj F.obj) ≫ 𝟙 _
  rw [Category.comp_id]
  exact scalarRestrictionSections_comp φ ψ X F.obj

end Langlands.Geometry.EtaleCohomologyAction
