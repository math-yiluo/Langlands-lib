import Langlands.Geometry.EtaleEquivariantPullbackFunctoriality

/-!
# Equality transport and coherence of equivariant étale pullback
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Cohomology EtalePullback

universe u w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y Z W : Scheme.{u}} (R : Type u) [CommRing R]
variable {G : Type w} [Group G]
variable (ρ : G →* (Aut X)ᵐᵒᵖ) (τ : G →* (Aut Y)ᵐᵒᵖ)
variable (υ : G →* (Aut Z)ᵐᵒᵖ) (σ : G →* (Aut W)ᵐᵒᵖ)

/-- Equal equivariant scheme maps have canonically isomorphic pullback functors. -/
def equivariantPullbackCongr {f k : Y ⟶ X} [Etale f] [Etale k]
    (hf : ∀ g, f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f)
    (hk : ∀ g, k ≫ (aut ρ g).hom = (aut τ g).hom ≫ k) (h : f = k) :
    equivariantPullback R ρ τ f hf ≅ equivariantPullback R ρ τ k hk := by
  subst k
  exact Iso.refl _

/-- Equality transport retains the ordinary restriction comparison. -/
@[simp] theorem equivariantPullbackCongr_hom_app_hom
    {f k : Y ⟶ X} [Etale f] [Etale k]
    (hf : ∀ g, f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f)
    (hk : ∀ g, k ≫ (aut ρ g).hom = (aut τ g).hom ≫ k)
    (h : f = k) (F : EquivariantSheaf R ρ) :
    ((equivariantPullbackCongr R ρ τ hf hk h).hom.app F).hom =
      (restrictionCongr R h).hom.app F.obj := by
  subst k
  rfl

/-- Equality transport is the identity for a reflexive equality. -/
@[simp] theorem equivariantPullbackCongr_refl
    (f : Y ⟶ X) [Etale f]
    (hf : ∀ g, f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f) :
    equivariantPullbackCongr R ρ τ hf hf rfl = Iso.refl _ := rfl

/-- Cohomology pullback respects equality of the equivariant scheme map. -/
theorem equivariantPullbackCohomology_congr {f k : Y ⟶ X} [Etale f] [Etale k]
    (hf : ∀ g, f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f)
    (hk : ∀ g, k ≫ (aut ρ g).hom = (aut τ g).hom ≫ k)
    (h : f = k) (q : ℕ) (F : EquivariantSheaf R ρ) :
    (equivariantPullbackCohomology R ρ τ f hf q).app F ≫
        (pullbackCohomologyFunctor R τ q).map
          ((equivariantPullbackCongr R ρ τ hf hk h).hom.app F) =
      (equivariantPullbackCohomology R ρ τ k hk q).app F := by
  subst k
  simp [equivariantPullbackCongr]

/-- Section pullback respects equality of the equivariant scheme map. -/
theorem equivariantPullbackSections_congr {f k : Y ⟶ X} [Etale f] [Etale k]
    (hf : ∀ g, f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f)
    (hk : ∀ g, k ≫ (aut ρ g).hom = (aut τ g).hom ≫ k)
    (h : f = k) (F : EquivariantSheaf R ρ) :
    (equivariantPullbackSections R ρ τ f hf).app F ≫
        (pullbackSectionsFunctor R τ).map
          ((equivariantPullbackCongr R ρ τ hf hk h).hom.app F) =
      (equivariantPullbackSections R ρ τ k hk).app F := by
  subst k
  simp [equivariantPullbackCongr]

/-- Component of forward restriction comparison along equal scheme morphisms. -/
theorem restrictionCongr_hom_component {f k : Y ⟶ X}
    [Etale f] [Etale k] (h : f = k)
    (F : EtaleDerivedSections.ModuleSheaf X R) (U : Y.Etaleᵒᵖ) :
    ((restrictionCongr R h).hom.app F).hom.app U =
      F.obj.map ((MorphismProperty.Over.mapCongr ⊤ h
        (inferInstance : Etale f)).inv.app U.unop).op := by
  subst k
  change 𝟙 _ = F.obj.map (𝟙 _)
  exact (F.obj.map_id _).symm

variable (f : Y ⟶ X) [Etale f]
variable (hf : ∀ g, f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f)

/-- The composition comparison with identity on the target is the unit comparison. -/
theorem equivariantPullbackComp_id_target (F : EquivariantSheaf R ρ) :
    (equivariantPullbackComp R ρ ρ τ (𝟙 X) f (equivariantMap_id ρ) hf).hom.app F ≫
        (equivariantPullbackCongr R ρ τ
          (equivariantMap_comp ρ ρ τ (𝟙 X) f (equivariantMap_id ρ) hf)
          hf (Category.comp_id f)).hom.app F =
      (equivariantPullback R ρ τ f hf).map ((equivariantPullbackId R ρ).hom.app F) := by
  apply TranslationAction.Equivariant.Hom.ext
  simp only [TranslationAction.Equivariant.comp_hom,
    equivariantPullbackComp_hom_app_hom, equivariantPullbackCongr_hom_app_hom,
    equivariantPullback_map_hom, equivariantPullbackId_hom_app_hom]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [restrictionCongr_hom_component]
  dsimp [restrictionComp, restrictionId, restriction]
  simp only [Category.comp_id, ← F.obj.obj.map_comp]
  congr 1

/-- The composition comparison with identity on the source is the unit comparison. -/
theorem equivariantPullbackComp_id_source (F : EquivariantSheaf R ρ) :
    (equivariantPullbackComp R ρ τ τ f (𝟙 Y) hf (equivariantMap_id τ)).hom.app F ≫
        (equivariantPullbackCongr R ρ τ
          (equivariantMap_comp ρ τ τ f (𝟙 Y) hf (equivariantMap_id τ))
          hf (Category.id_comp f)).hom.app F =
      (equivariantPullbackId R τ).hom.app ((equivariantPullback R ρ τ f hf).obj F) := by
  apply TranslationAction.Equivariant.Hom.ext
  simp only [TranslationAction.Equivariant.comp_hom,
    equivariantPullbackComp_hom_app_hom, equivariantPullbackCongr_hom_app_hom,
    equivariantPullbackId_hom_app_hom]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [restrictionCongr_hom_component]
  dsimp [restrictionComp, restrictionId, restriction, equivariantPullback,
    equivariantPullbackObj]
  simp only [Category.comp_id, ← F.obj.obj.map_comp]
  congr 1

variable (k : Z ⟶ Y) [Etale k] (l : W ⟶ Z) [Etale l]
variable (hk : ∀ g, k ≫ (aut τ g).hom = (aut υ g).hom ≫ k)
variable (hl : ∀ g, l ≫ (aut υ g).hom = (aut σ g).hom ≫ l)

/-- The two iterated composition comparisons agree after scheme associativity transport. -/
theorem equivariantPullbackComp_assoc (F : EquivariantSheaf R ρ) :
    (equivariantPullbackComp R τ υ σ k l hk hl).hom.app
        ((equivariantPullback R ρ τ f hf).obj F) ≫
      (equivariantPullbackComp R ρ τ σ f (l ≫ k) hf
        (equivariantMap_comp τ υ σ k l hk hl)).hom.app F ≫
      (equivariantPullbackCongr R ρ σ
        (equivariantMap_comp ρ τ σ f (l ≫ k) hf
          (equivariantMap_comp τ υ σ k l hk hl))
        (equivariantMap_comp ρ υ σ (k ≫ f) l
          (equivariantMap_comp ρ τ υ f k hf hk) hl)
        (Category.assoc l k f)).hom.app F =
    (equivariantPullback R υ σ l hl).map
        ((equivariantPullbackComp R ρ τ υ f k hf hk).hom.app F) ≫
      (equivariantPullbackComp R ρ υ σ (k ≫ f) l
        (equivariantMap_comp ρ τ υ f k hf hk) hl).hom.app F := by
  apply TranslationAction.Equivariant.Hom.ext
  simp only [TranslationAction.Equivariant.comp_hom,
    equivariantPullbackComp_hom_app_hom, equivariantPullbackCongr_hom_app_hom,
    equivariantPullback_map_hom]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [restrictionCongr_hom_component]
  dsimp [restrictionComp, restriction, equivariantPullback, equivariantPullbackObj]
  simp only [← F.obj.obj.map_comp]
  congr 1

end Langlands.Geometry.EtaleCohomologyAction
