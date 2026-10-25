import Langlands.Geometry.EtaleEquivariantScalarExtension
import Langlands.Geometry.EtaleEquivariantPullbackFunctoriality

/-!
# Equivariant scalar extension and geometric pullback
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry EtalePullback Langlands.Cohomology

universe u w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
variable {X Y Z : Scheme.{u}} {G : Type w} [Group G]
variable (ρ : G →* (Aut X)ᵐᵒᵖ) (τ : G →* (Aut Y)ᵐᵒᵖ)
variable (f : Y ⟶ X) [Etale f]
variable (hf : ∀ g, f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f)

/-- The inverse pullback comparison is the equivariant lift of the restricted unit. -/
def scalarExtensionPullbackInv (F : EquivariantSheaf R ρ) :
    (scalarExtensionFunctor φ τ).obj ((equivariantPullback R ρ τ f hf).obj F) ⟶
      (equivariantPullback S ρ τ f hf).obj ((scalarExtensionFunctor φ ρ).obj F) :=
  scalarExtensionLift φ τ
    ((equivariantPullback R ρ τ f hf).map ((scalarExtensionUnit φ ρ).app F) ≫
      (scalarRestrictionEquivariantPullbackIso φ ρ τ f hf).hom.app
        ((scalarExtensionFunctor φ ρ).obj F))

/-- The constructed equivariant lift has the ordinary inverse comparison as its map. -/
theorem scalarExtensionPullbackInv_hom (F : EquivariantSheaf R ρ) :
    (scalarExtensionPullbackInv φ ρ τ f hf F).hom =
      (sheafExtendScalarsPullbackIso φ f).inv.app F.obj := by
  symm
  apply sheafExtensionLift_unique φ Y
  change (sheafExtensionUnit φ Y).app
      ((restriction f (ModuleCat.{u} R)).obj F.obj) ≫
        (sheafRestrictScalars φ Y).map
          ((sheafExtendScalarsPullbackIso φ f).inv.app F.obj) =
    (restriction f (ModuleCat.{u} R)).map ((sheafExtensionUnit φ X).app F.obj) ≫ 𝟙 _
  rw [← sheafExtensionUnit_pullback φ f F.obj, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app]
  erw [(sheafRestrictScalars φ Y).map_id]
  rfl

/-- The ordinary pullback isomorphism lifts to geometric equivariant sheaves. -/
def scalarExtensionPullbackObjIso (F : EquivariantSheaf R ρ) :
    (equivariantPullback S ρ τ f hf).obj ((scalarExtensionFunctor φ ρ).obj F) ≅
      (scalarExtensionFunctor φ τ).obj ((equivariantPullback R ρ τ f hf).obj F) :=
  (TranslationAction.Equivariant.mkIso
    ((sheafExtendScalarsPullbackIso φ f).app F.obj).symm (fun g => by
      have h := (scalarExtensionPullbackInv φ ρ τ f hf F).comm g
      rw [scalarExtensionPullbackInv_hom] at h
      exact h)).symm

/-- Extension of scalars commutes naturally with equivariant etale pullback. -/
def scalarExtensionEquivariantPullbackIso :
    scalarExtensionFunctor φ ρ ⋙ equivariantPullback S ρ τ f hf ≅
      equivariantPullback R ρ τ f hf ⋙ scalarExtensionFunctor φ τ :=
  NatIso.ofComponents (scalarExtensionPullbackObjIso φ ρ τ f hf)
    (fun a => by
      apply TranslationAction.Equivariant.Hom.ext
      exact (sheafExtendScalarsPullbackIso φ f).hom.naturality a.hom)

/-- Forgetting equivariance gives the ordinary forward pullback comparison. -/
@[simp] theorem scalarExtensionEquivariantPullbackIso_hom_app_hom
    (F : EquivariantSheaf R ρ) :
    ((scalarExtensionEquivariantPullbackIso φ ρ τ f hf).hom.app F).hom =
      (sheafExtendScalarsPullbackIso φ f).hom.app F.obj := rfl

/-- Forgetting equivariance gives the ordinary inverse pullback comparison. -/
@[simp] theorem scalarExtensionEquivariantPullbackIso_inv_app_hom
    (F : EquivariantSheaf R ρ) :
    ((scalarExtensionEquivariantPullbackIso φ ρ τ f hf).inv.app F).hom =
      (sheafExtendScalarsPullbackIso φ f).inv.app F.obj := rfl

/-- The equivariant comparison respects the extension units. -/
theorem scalarExtensionUnit_equivariantPullback (F : EquivariantSheaf R ρ) :
    (equivariantPullback R ρ τ f hf).map ((scalarExtensionUnit φ ρ).app F) ≫
      (scalarRestrictionEquivariantPullbackIso φ ρ τ f hf).hom.app
        ((scalarExtensionFunctor φ ρ).obj F) ≫
      (scalarRestrictionFunctor φ τ).map
        ((scalarExtensionEquivariantPullbackIso φ ρ τ f hf).hom.app F) =
    (scalarExtensionUnit φ τ).app ((equivariantPullback R ρ τ f hf).obj F) := by
  apply TranslationAction.Equivariant.Hom.ext
  change _ ≫ 𝟙 _ ≫ _ = _
  rw [Category.id_comp]
  exact sheafExtensionUnit_pullback φ f F.obj

set_option maxHeartbeats 800000 in
/-- The scalar-extension comparison respects identity geometric pullback. -/
theorem scalarExtensionEquivariantPullbackIso_id (F : EquivariantSheaf R ρ) :
    (scalarExtensionEquivariantPullbackIso φ ρ ρ (𝟙 X) (equivariantMap_id ρ)).hom.app F ≫
      (scalarExtensionFunctor φ ρ).map ((equivariantPullbackId R ρ).hom.app F) =
    (equivariantPullbackId S ρ).hom.app ((scalarExtensionFunctor φ ρ).obj F) := by
  apply TranslationAction.Equivariant.Hom.ext
  exact sheafExtendScalarsPullbackIso_id φ F.obj

variable (υ : G →* (Aut Z)ᵐᵒᵖ) (k : Z ⟶ Y) [Etale k]
variable (hk : ∀ g, k ≫ (aut τ g).hom = (aut υ g).hom ≫ k)

/-- The scalar-extension comparisons respect composition of equivariant etale maps. -/
theorem scalarExtensionEquivariantPullbackIso_comp (F : EquivariantSheaf R ρ) :
    (scalarExtensionEquivariantPullbackIso φ ρ υ (k ≫ f)
        (equivariantMap_comp ρ τ υ f k hf hk)).hom.app F ≫
      (scalarExtensionFunctor φ υ).map
        ((equivariantPullbackComp R ρ τ υ f k hf hk).inv.app F) =
    (equivariantPullbackComp S ρ τ υ f k hf hk).inv.app
        ((scalarExtensionFunctor φ ρ).obj F) ≫
      (equivariantPullback S τ υ k hk).map
        ((scalarExtensionEquivariantPullbackIso φ ρ τ f hf).hom.app F) ≫
      (scalarExtensionEquivariantPullbackIso φ τ υ k hk).hom.app
        ((equivariantPullback R ρ τ f hf).obj F) := by
  apply TranslationAction.Equivariant.Hom.ext
  exact sheafExtendScalarsPullbackIso_comp φ f k F.obj

end Langlands.Geometry.EtaleCohomologyAction
