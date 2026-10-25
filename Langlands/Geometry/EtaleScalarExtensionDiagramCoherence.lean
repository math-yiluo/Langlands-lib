import Langlands.Geometry.EtaleScalarDiagramAdjunction
import Langlands.Geometry.EtaleScalarDiagramCoherence
import Langlands.Geometry.EtaleEquivariantScalarExtensionCoherence

/-!
# Identity and composition for scalar extension of coefficient diagrams
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry Langlands.Cohomology

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

/-- Evaluation of scalar extension on a diagram morphism is pointwise extension. -/
@[simp] theorem extendScalarsFunctor_map_app
    {D E : EquivariantCoefficientDiagram R S ρ hρ} (α : D ⟶ E) (i : J) :
    ((extendScalarsFunctor φ).map α).app i =
      (scalarExtensionFunctor φ (ρ i)).map (α.app i) := rfl

/-- Evaluation of scalar restriction on a diagram morphism is pointwise restriction. -/
@[simp] theorem restrictScalarsFunctor_map_app
    {D E : EquivariantCoefficientDiagram A S ρ hρ} (α : D ⟶ E) (i : J) :
    ((restrictScalarsFunctor φ).map α).app i =
      (scalarRestrictionFunctor φ (ρ i)).map (α.app i) := rfl

/-- Extension by the identity is canonically the identity on coefficient diagrams. -/
def extendScalarsIdIso :
    extendScalarsFunctor (S := S) (ρ := ρ) (hρ := hρ) (RingHom.id R) ≅
      𝟭 (EquivariantCoefficientDiagram R S ρ hρ) :=
  (conjugateIsoEquiv Adjunction.id
    (extensionRestrictionAdj (RingHom.id R))).symm restrictScalarsIdIso.symm

/-- Extension by a composite is canonically successive extension of diagrams. -/
def extendScalarsCompIso :
    extendScalarsFunctor (S := S) (ρ := ρ) (hρ := hρ) (ψ.comp φ) ≅
      extendScalarsFunctor φ ⋙ extendScalarsFunctor ψ :=
  (conjugateIsoEquiv
    ((extensionRestrictionAdj φ).comp (extensionRestrictionAdj ψ))
    (extensionRestrictionAdj (ψ.comp φ))).symm (restrictScalarsCompIso φ ψ).symm

/-- Evaluation of the identity comparison gives the equivariant sheaf comparison. -/
@[simp] theorem extendScalarsIdIso_hom_app_app
    (D : EquivariantCoefficientDiagram R S ρ hρ) (i : J) :
    ((extendScalarsIdIso).hom.app D).app i =
      (scalarExtensionIdIso (ρ i)).hom.app (D.obj i) := by
  simp only [extendScalarsIdIso, scalarExtensionIdIso, conjugateIsoEquiv_symm_apply_hom,
    conjugateEquiv_symm_apply_app]
  simp only [comp_app, extendScalarsFunctor_map_app,
    extensionRestrictionAdj_counit_app]
  rfl

/-- Evaluation of the inverse identity comparison gives the inverse sheaf comparison. -/
@[simp] theorem extendScalarsIdIso_inv_app_app
    (D : EquivariantCoefficientDiagram R S ρ hρ) (i : J) :
    ((extendScalarsIdIso).inv.app D).app i =
      (scalarExtensionIdIso (ρ i)).inv.app (D.obj i) := rfl

/-- Evaluation of the composition comparison gives the equivariant sheaf comparison. -/
@[simp] theorem extendScalarsCompIso_hom_app_app
    (D : EquivariantCoefficientDiagram R S ρ hρ) (i : J) :
    ((extendScalarsCompIso φ ψ).hom.app D).app i =
      (scalarExtensionCompIso φ ψ (ρ i)).hom.app (D.obj i) := by
  simp only [extendScalarsCompIso, scalarExtensionCompIso, conjugateIsoEquiv_symm_apply_hom,
    conjugateEquiv_symm_apply_app, Adjunction.comp_unit_app]
  simp only [comp_app, extendScalarsFunctor_map_app,
    restrictScalarsFunctor_map_app, extensionRestrictionAdj_unit_app,
    extensionRestrictionAdj_counit_app]
  rfl

/-- Evaluation of the inverse composition comparison gives the inverse sheaf comparison. -/
@[simp] theorem extendScalarsCompIso_inv_app_app
    (D : EquivariantCoefficientDiagram R S ρ hρ) (i : J) :
    ((extendScalarsCompIso φ ψ).inv.app D).app i =
      (scalarExtensionCompIso φ ψ (ρ i)).inv.app (D.obj i) := by
  simp only [extendScalarsCompIso, scalarExtensionCompIso, conjugateIsoEquiv_symm_apply_inv,
    conjugateEquiv_symm_apply_app, Adjunction.comp_counit_app]
  simp only [comp_app, Functor.comp_map, extendScalarsFunctor_map_app,
    extensionRestrictionAdj_unit_app, extensionRestrictionAdj_counit_app]
  rfl

/-- The identity extension comparison is conjugate to inverse identity restriction. -/
@[simp] theorem conjugate_extendScalarsIdIso_hom :
    conjugateEquiv Adjunction.id
      (extensionRestrictionAdj (S := S) (ρ := ρ) (hρ := hρ) (RingHom.id R))
      extendScalarsIdIso.hom = restrictScalarsIdIso.inv :=
  (conjugateEquiv _ _).apply_symm_apply _

/-- The composite extension comparison is conjugate to inverse composite restriction. -/
@[simp] theorem conjugate_extendScalarsCompIso_hom :
    conjugateEquiv
      ((extensionRestrictionAdj (S := S) (ρ := ρ) (hρ := hρ) φ).comp
        (extensionRestrictionAdj ψ))
      (extensionRestrictionAdj (ψ.comp φ))
      (extendScalarsCompIso φ ψ).hom = (restrictScalarsCompIso φ ψ).inv :=
  (conjugateEquiv _ _).apply_symm_apply _

/-- The identity comparison carries the diagram unit to inverse identity restriction. -/
theorem extensionUnit_id (D : EquivariantCoefficientDiagram R S ρ hρ) :
    extensionUnitApp (RingHom.id R) D ≫
        (restrictScalarsFunctor (RingHom.id R)).map (extendScalarsIdIso.hom.app D) =
      restrictScalarsIdIso.inv.app D := by
  apply Hom.ext
  funext i
  simp only [comp_app, restrictScalarsFunctor_map_app,
    extendScalarsIdIso_hom_app_app, restrictScalarsIdIso_inv_app_app]
  exact scalarExtensionUnit_id (ρ i) (D.obj i)

/-- The composite comparison carries one diagram unit to the two successive units. -/
theorem extensionUnit_comp (D : EquivariantCoefficientDiagram R S ρ hρ) :
    extensionUnitApp (ψ.comp φ) D ≫
        (restrictScalarsFunctor (ψ.comp φ)).map ((extendScalarsCompIso φ ψ).hom.app D) =
      extensionUnitApp φ D ≫
        (restrictScalarsFunctor φ).map (extensionUnitApp ψ (extendScalars φ D)) ≫
        (restrictScalarsCompIso φ ψ).inv.app (extendScalars ψ (extendScalars φ D)) := by
  apply Hom.ext
  funext i
  simp only [comp_app, restrictScalarsFunctor_map_app,
    extendScalarsCompIso_hom_app_app, restrictScalarsCompIso_inv_app_app]
  exact scalarExtensionUnit_comp φ ψ (ρ i) (D.obj i)

/-- Splitting off extension by the source identity and removing it is identity. -/
theorem extendScalarsCompIso_id_left :
    (extendScalarsCompIso (S := S) (ρ := ρ) (hρ := hρ) (RingHom.id R) φ).hom ≫
        Functor.whiskerRight extendScalarsIdIso.hom (extendScalarsFunctor φ) ≫
        (Functor.leftUnitor (extendScalarsFunctor φ)).hom =
      𝟙 (extendScalarsFunctor φ) := by
  apply NatTrans.ext
  funext D
  apply Hom.ext
  funext i
  simp only [NatTrans.comp_app, comp_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, extendScalarsFunctor_map_app,
    extendScalarsCompIso_hom_app_app, extendScalarsIdIso_hom_app_app,
    NatTrans.id_app, id_app]
  exact congrArg (fun a => a.app (D.obj i)) (scalarExtensionCompIso_id_left φ (ρ i))

/-- Splitting off extension by the target identity and removing it is identity. -/
theorem extendScalarsCompIso_id_right :
    (extendScalarsCompIso (S := S) (ρ := ρ) (hρ := hρ) φ (RingHom.id A)).hom ≫
        Functor.whiskerLeft (extendScalarsFunctor φ) extendScalarsIdIso.hom ≫
        (Functor.rightUnitor (extendScalarsFunctor φ)).hom =
      𝟙 (extendScalarsFunctor φ) := by
  apply NatTrans.ext
  funext D
  apply Hom.ext
  funext i
  simp only [NatTrans.comp_app, comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, extendScalarsCompIso_hom_app_app,
    extendScalarsIdIso_hom_app_app, NatTrans.id_app, id_app]
  exact congrArg (fun a => a.app (D.obj i)) (scalarExtensionCompIso_id_right φ (ρ i))

/-- The two ways to split three coefficient extensions agree after associating functors. -/
theorem extendScalarsCompIso_assoc :
    (extendScalarsCompIso (S := S) (ρ := ρ) (hρ := hρ) (ψ.comp φ) χ).hom ≫
        Functor.whiskerRight (extendScalarsCompIso φ ψ).hom (extendScalarsFunctor χ) ≫
        (Functor.associator (extendScalarsFunctor φ)
          (extendScalarsFunctor ψ) (extendScalarsFunctor χ)).hom =
      (extendScalarsCompIso φ (χ.comp ψ)).hom ≫
        Functor.whiskerLeft (extendScalarsFunctor φ) (extendScalarsCompIso ψ χ).hom := by
  apply NatTrans.ext
  funext D
  apply Hom.ext
  funext i
  simp only [NatTrans.comp_app, comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app,
    extendScalarsFunctor_map_app, extendScalarsCompIso_hom_app_app, id_app]
  exact congrArg (fun a => a.app (D.obj i)) (scalarExtensionCompIso_assoc φ ψ χ (ρ i))

end EquivariantCoefficientDiagram

end Langlands.Geometry.EtaleCohomologyAction
