import Langlands.Geometry.EtaleScalarExtensionDiagram
import Langlands.Geometry.EtaleScalarDiagram

/-!
# Scalar extension and restriction on compatible coefficient diagrams
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

section PullbackLift

variable {X Y : Scheme.{u}} {G : Type t} [Group G]
variable (ρ : G →* (Aut X)ᵐᵒᵖ) (τ : G →* (Aut Y)ᵐᵒᵖ)
variable (f : Y ⟶ X) [Etale f]
variable (hf : ∀ g, f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f)

/-- Universal scalar extension commutes with equivariant geometric restriction. -/
theorem scalarExtensionLift_equivariantPullback
    {F : EquivariantSheaf R ρ} {E : EquivariantSheaf A ρ}
    (a : F ⟶ (scalarRestrictionFunctor φ ρ).obj E) :
    (scalarExtensionEquivariantPullbackIso φ ρ τ f hf).hom.app F ≫
      scalarExtensionLift φ τ
        ((equivariantPullback R ρ τ f hf).map a ≫
          (scalarRestrictionEquivariantPullbackIso φ ρ τ f hf).hom.app E) =
    (equivariantPullback A ρ τ f hf).map (scalarExtensionLift φ ρ a) := by
  have h : (scalarExtensionEquivariantPullbackIso φ ρ τ f hf).inv.app F ≫
      (equivariantPullback A ρ τ f hf).map (scalarExtensionLift φ ρ a) =
    scalarExtensionLift φ τ
      ((equivariantPullback R ρ τ f hf).map a ≫
        (scalarRestrictionEquivariantPullbackIso φ ρ τ f hf).hom.app E) := by
    apply scalarExtensionLift_unique
    rw [← scalarExtensionUnit_equivariantPullback φ ρ τ f hf F]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    erw [(scalarRestrictionFunctor φ τ).map_id]
    rw [Category.id_comp]
    erw [← (scalarRestrictionEquivariantPullbackIso φ ρ τ f hf).hom.naturality
      (scalarExtensionLift φ ρ a)]
    simp only [Functor.comp_map, ← Category.assoc, ← Functor.map_comp,
      scalarExtensionUnit_lift]
  rw [← h, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

end PullbackLift

variable {J : Type v} [Category.{w} J] {S : J ⥤ Scheme.{u}ᵒᵖ}
variable [∀ {i j : J} (a : i ⟶ j), Etale (S.map a).unop]
variable {G : Type t} [Group G] {ρ : ∀ i, G →* (Aut (S.obj i).unop)ᵐᵒᵖ}
variable {hρ : ∀ {i j : J} (a : i ⟶ j) (g : G),
  (S.map a).unop ≫ (aut (ρ i) g).hom = (aut (ρ j) g).hom ≫ (S.map a).unop}

namespace EquivariantCoefficientDiagram

/-- The pointwise extension units form a compatible coefficient morphism. -/
def extensionUnitApp (D : EquivariantCoefficientDiagram R S ρ hρ) :
    D ⟶ restrictScalars φ (extendScalars φ D) where
  app i := (scalarExtensionUnit φ (ρ i)).app (D.obj i)
  comm {i j} a := by
    apply TranslationAction.Equivariant.Hom.ext
    change (D.map a).hom ≫ (sheafExtensionUnit φ (S.obj j).unop).app (D.obj j).obj =
      (restriction (S.map a).unop (ModuleCat.{u} R)).map
          ((sheafExtensionUnit φ (S.obj i).unop).app (D.obj i).obj) ≫
        (𝟙 _ ≫ (sheafRestrictScalars φ (S.obj j).unop).map
          ((sheafExtendScalarsPullbackIso φ (S.map a).unop).hom.app (D.obj i).obj ≫
            (sheafExtendScalars φ (S.obj j).unop).map (D.map a).hom))
    rw [Category.id_comp, Functor.map_comp, ← Category.assoc, sheafExtensionUnit_pullback]
    exact (sheafExtensionUnit φ (S.obj j).unop).naturality (D.map a).hom

/-- The scalar-extension unit is natural in compatible coefficient diagrams. -/
def extensionUnit :
    𝟭 (EquivariantCoefficientDiagram R S ρ hρ) ⟶
      extendScalarsFunctor φ ⋙ restrictScalarsFunctor φ where
  app := extensionUnitApp φ
  naturality {D E} α := by
    apply Hom.ext
    funext i
    exact (scalarExtensionUnit φ (ρ i)).naturality (α.app i)

/-- The universal equivariant lifts respect all coefficient transitions. -/
def extensionLift {D : EquivariantCoefficientDiagram R S ρ hρ}
    {E : EquivariantCoefficientDiagram A S ρ hρ} (α : D ⟶ restrictScalars φ E) :
    extendScalars φ D ⟶ E where
  app i := scalarExtensionLift φ (ρ i) (α.app i)
  comm {i j} a := by
    dsimp only [extendScalars]
    rw [Category.assoc, ← scalarExtensionLift_precomp, α.comm]
    change _ ≫ scalarExtensionLift φ (ρ j)
      ((equivariantDiagramRestriction R S ρ hρ a).map (α.app i) ≫
        ((scalarRestrictionEquivariantPullbackIso φ (ρ i) (ρ j)
          (S.map a).unop (hρ a)).hom.app (E.obj i) ≫
            (scalarRestrictionFunctor φ (ρ j)).map (E.map a))) = _
    rw [← Category.assoc ((equivariantDiagramRestriction R S ρ hρ a).map (α.app i)),
      scalarExtensionLift_postcomp, ← Category.assoc,
      scalarExtensionLift_equivariantPullback]

/-- The compatible lift factors the original morphism through the diagram unit. -/
@[simp] theorem extensionUnit_lift {D : EquivariantCoefficientDiagram R S ρ hρ}
    {E : EquivariantCoefficientDiagram A S ρ hρ} (α : D ⟶ restrictScalars φ E) :
    extensionUnitApp φ D ≫ (restrictScalarsFunctor φ).map (extensionLift φ α) = α := by
  apply Hom.ext
  funext i
  exact scalarExtensionUnit_lift φ (ρ i) (α.app i)

/-- A compatible morphism satisfying the unit equation is the universal lift. -/
theorem extensionLift_unique {D : EquivariantCoefficientDiagram R S ρ hρ}
    {E : EquivariantCoefficientDiagram A S ρ hρ} (α : D ⟶ restrictScalars φ E)
    (β : extendScalars φ D ⟶ E)
    (h : extensionUnitApp φ D ≫ (restrictScalarsFunctor φ).map β = α) :
    β = extensionLift φ α := by
  apply Hom.ext
  funext i
  exact scalarExtensionLift_unique φ (ρ i) (α.app i) (β.app i)
    (congrArg (fun γ => γ.app i) h)

/-- The universal correspondence between compatible equivariant coefficient morphisms. -/
def extensionHomEquiv (D : EquivariantCoefficientDiagram R S ρ hρ)
    (E : EquivariantCoefficientDiagram A S ρ hρ) :
    (extendScalars φ D ⟶ E) ≃ (D ⟶ restrictScalars φ E) where
  toFun β := extensionUnitApp φ D ≫ (restrictScalarsFunctor φ).map β
  invFun := extensionLift φ
  left_inv β := (extensionLift_unique φ _ β rfl).symm
  right_inv := extensionUnit_lift φ

/-- The diagram hom correspondence evaluates to the pointwise equivariant correspondence. -/
@[simp] theorem extensionHomEquiv_app (D : EquivariantCoefficientDiagram R S ρ hρ)
    (E : EquivariantCoefficientDiagram A S ρ hρ) (β : extendScalars φ D ⟶ E) (i : J) :
    (extensionHomEquiv φ D E β).app i =
      scalarExtensionHomEquiv φ (ρ i) (D.obj i) (E.obj i) (β.app i) := rfl

/-- The inverse correspondence is the pointwise universal lift. -/
@[simp] theorem extensionHomEquiv_symm_app (D : EquivariantCoefficientDiagram R S ρ hρ)
    (E : EquivariantCoefficientDiagram A S ρ hρ) (α : D ⟶ restrictScalars φ E) (i : J) :
    ((extensionHomEquiv φ D E).symm α).app i =
      scalarExtensionLift φ (ρ i) (α.app i) := rfl

/-- Scalar extension is left adjoint to restriction on compatible coefficient diagrams. -/
def extensionRestrictionAdj :
    extendScalarsFunctor (S := S) (ρ := ρ) (hρ := hρ) φ ⊣ restrictScalarsFunctor φ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := extensionHomEquiv φ
      homEquiv_naturality_left_symm := fun {D' D E} α β => by
        apply Hom.ext
        funext i
        exact scalarExtensionLift_precomp φ (ρ i) (α.app i) (β.app i)
      homEquiv_naturality_right := fun {D E E'} α β => by
        apply Hom.ext
        funext i
        exact (scalarExtensionRestrictionAdj φ (ρ i)).homEquiv_naturality_right
          (α.app i) (β.app i) }

instance : (extendScalarsFunctor (S := S) (ρ := ρ) (hρ := hρ) φ).IsLeftAdjoint :=
  (extensionRestrictionAdj φ).isLeftAdjoint

/-- The packaged adjunction has exactly the constructed universal correspondence. -/
theorem extensionRestrictionAdj_homEquiv (D : EquivariantCoefficientDiagram R S ρ hρ)
    (E : EquivariantCoefficientDiagram A S ρ hρ) :
    (extensionRestrictionAdj φ).homEquiv D E = extensionHomEquiv φ D E := by
  exact congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) D) E

/-- The packaged adjunction unit is the constructed compatible unit. -/
@[simp] theorem extensionRestrictionAdj_unit_app
    (D : EquivariantCoefficientDiagram R S ρ hρ) :
    (extensionRestrictionAdj φ).unit.app D = extensionUnitApp φ D := by
  rw [← Adjunction.homEquiv_id, extensionRestrictionAdj_homEquiv]
  change extensionUnitApp φ D ≫ (restrictScalarsFunctor φ).map (𝟙 _) = _
  erw [(restrictScalarsFunctor φ).map_id]
  exact Category.comp_id _

/-- Evaluation of the packaged counit is the pointwise equivariant counit. -/
@[simp] theorem extensionRestrictionAdj_counit_app
    (E : EquivariantCoefficientDiagram A S ρ hρ) (i : J) :
    ((extensionRestrictionAdj φ).counit.app E).app i =
      (scalarExtensionCounit φ (ρ i)).app (E.obj i) := by
  rw [← Adjunction.homEquiv_symm_id, extensionRestrictionAdj_homEquiv]
  change scalarExtensionLift φ (ρ i) (𝟙 _) = _
  exact (scalarExtensionRestrictionAdj φ (ρ i)).homEquiv_symm_id (E.obj i)

end EquivariantCoefficientDiagram

end Langlands.Geometry.EtaleCohomologyAction
