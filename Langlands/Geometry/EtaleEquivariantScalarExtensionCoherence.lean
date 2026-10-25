import Langlands.Geometry.EtaleEquivariantScalarExtension
import Langlands.Geometry.EtaleScalarExtensionCoherence

/-!
# Identity and composition for equivariant scalar extension
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry Langlands.Cohomology

universe u w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
variable (φ : R →+* A) (ψ : A →+* B) (χ : B →+* C)
variable {X : Scheme.{u}} {G : Type w} [Group G] (ρ : G →* (Aut X)ᵐᵒᵖ)

/-- Extension by the identity is canonically the identity on equivariant coefficient sheaves. -/
def scalarExtensionIdIso :
    scalarExtensionFunctor (RingHom.id R) ρ ≅ 𝟭 (EquivariantSheaf R ρ) :=
  (conjugateIsoEquiv Adjunction.id
    (scalarExtensionRestrictionAdj (RingHom.id R) ρ)).symm
      (scalarRestrictionIdIso ρ).symm

/-- Extension by a composite is canonically successive equivariant extension. -/
def scalarExtensionCompIso :
    scalarExtensionFunctor (ψ.comp φ) ρ ≅
      scalarExtensionFunctor φ ρ ⋙ scalarExtensionFunctor ψ ρ :=
  (conjugateIsoEquiv
    ((scalarExtensionRestrictionAdj φ ρ).comp (scalarExtensionRestrictionAdj ψ ρ))
    (scalarExtensionRestrictionAdj (ψ.comp φ) ρ)).symm
      (scalarRestrictionCompIso φ ψ ρ).symm

/-- Forgetting equivariance recovers the ordinary identity comparison. -/
@[simp] theorem scalarExtensionIdIso_hom_app_hom (F : EquivariantSheaf R ρ) :
    ((scalarExtensionIdIso ρ).hom.app F).hom =
      (sheafExtendScalarsIdIso X).hom.app F.obj := rfl

/-- The inverse identity comparison forgets to the ordinary inverse. -/
@[simp] theorem scalarExtensionIdIso_inv_app_hom (F : EquivariantSheaf R ρ) :
    ((scalarExtensionIdIso ρ).inv.app F).hom =
      (sheafExtendScalarsIdIso X).inv.app F.obj := rfl

/-- Forgetting equivariance recovers the ordinary composite comparison. -/
@[simp] theorem scalarExtensionCompIso_hom_app_hom (F : EquivariantSheaf R ρ) :
    ((scalarExtensionCompIso φ ψ ρ).hom.app F).hom =
      (sheafExtendScalarsCompIso φ ψ X).hom.app F.obj := rfl

/-- The inverse composite comparison forgets to the ordinary inverse. -/
@[simp] theorem scalarExtensionCompIso_inv_app_hom (F : EquivariantSheaf R ρ) :
    ((scalarExtensionCompIso φ ψ ρ).inv.app F).hom =
      (sheafExtendScalarsCompIso φ ψ X).inv.app F.obj := rfl

/-- The identity extension comparison is conjugate to inverse identity restriction. -/
@[simp] theorem conjugate_scalarExtensionIdIso_hom :
    conjugateEquiv Adjunction.id (scalarExtensionRestrictionAdj (RingHom.id R) ρ)
      (scalarExtensionIdIso ρ).hom = (scalarRestrictionIdIso ρ).inv :=
  (conjugateEquiv _ _).apply_symm_apply _

/-- The composite extension comparison is conjugate to inverse composite restriction. -/
@[simp] theorem conjugate_scalarExtensionCompIso_hom :
    conjugateEquiv
      ((scalarExtensionRestrictionAdj φ ρ).comp (scalarExtensionRestrictionAdj ψ ρ))
      (scalarExtensionRestrictionAdj (ψ.comp φ) ρ)
      (scalarExtensionCompIso φ ψ ρ).hom =
        (scalarRestrictionCompIso φ ψ ρ).inv :=
  (conjugateEquiv _ _).apply_symm_apply _

/-- The identity comparison carries the extension unit to inverse identity restriction. -/
theorem scalarExtensionUnit_id (F : EquivariantSheaf R ρ) :
    (scalarExtensionUnit (RingHom.id R) ρ).app F ≫
        (scalarRestrictionFunctor (RingHom.id R) ρ).map
          ((scalarExtensionIdIso ρ).hom.app F) =
      (scalarRestrictionIdIso ρ).inv.app F := by
  apply TranslationAction.Equivariant.Hom.ext
  exact sheafExtensionUnit_id X F.obj

/-- The composite comparison carries one extension unit to the two successive units. -/
theorem scalarExtensionUnit_comp (F : EquivariantSheaf R ρ) :
    (scalarExtensionUnit (ψ.comp φ) ρ).app F ≫
        (scalarRestrictionFunctor (ψ.comp φ) ρ).map
          ((scalarExtensionCompIso φ ψ ρ).hom.app F) =
      (scalarExtensionUnit φ ρ).app F ≫
        (scalarRestrictionFunctor φ ρ).map
          ((scalarExtensionUnit ψ ρ).app ((scalarExtensionFunctor φ ρ).obj F)) ≫
        (scalarRestrictionCompIso φ ψ ρ).inv.app
          ((scalarExtensionFunctor ψ ρ).obj ((scalarExtensionFunctor φ ρ).obj F)) := by
  apply TranslationAction.Equivariant.Hom.ext
  exact sheafExtensionUnit_comp φ ψ X F.obj

/-- Splitting off extension by the source identity and removing it is identity. -/
theorem scalarExtensionCompIso_id_left :
    (scalarExtensionCompIso (RingHom.id R) φ ρ).hom ≫
        Functor.whiskerRight (scalarExtensionIdIso ρ).hom (scalarExtensionFunctor φ ρ) ≫
        (Functor.leftUnitor (scalarExtensionFunctor φ ρ)).hom =
      𝟙 (scalarExtensionFunctor φ ρ) := by
  apply NatTrans.ext
  funext F
  apply TranslationAction.Equivariant.Hom.ext
  exact congrArg (fun a => a.app F.obj)
    (sheafExtendScalarsCompIso_id_left φ X)

/-- Splitting off extension by the target identity and removing it is identity. -/
theorem scalarExtensionCompIso_id_right :
    (scalarExtensionCompIso φ (RingHom.id A) ρ).hom ≫
        Functor.whiskerLeft (scalarExtensionFunctor φ ρ) (scalarExtensionIdIso ρ).hom ≫
        (Functor.rightUnitor (scalarExtensionFunctor φ ρ)).hom =
      𝟙 (scalarExtensionFunctor φ ρ) := by
  apply NatTrans.ext
  funext F
  apply TranslationAction.Equivariant.Hom.ext
  exact congrArg (fun a => a.app F.obj)
    (sheafExtendScalarsCompIso_id_right φ X)

/-- The two ways to split three coefficient extensions agree after associating functors. -/
theorem scalarExtensionCompIso_assoc :
    (scalarExtensionCompIso (ψ.comp φ) χ ρ).hom ≫
        Functor.whiskerRight (scalarExtensionCompIso φ ψ ρ).hom
          (scalarExtensionFunctor χ ρ) ≫
        (Functor.associator (scalarExtensionFunctor φ ρ)
          (scalarExtensionFunctor ψ ρ) (scalarExtensionFunctor χ ρ)).hom =
      (scalarExtensionCompIso φ (χ.comp ψ) ρ).hom ≫
        Functor.whiskerLeft (scalarExtensionFunctor φ ρ)
          (scalarExtensionCompIso ψ χ ρ).hom := by
  apply NatTrans.ext
  funext F
  apply TranslationAction.Equivariant.Hom.ext
  exact congrArg (fun a => a.app F.obj)
    (sheafExtendScalarsCompIso_assoc φ ψ χ X)

end Langlands.Geometry.EtaleCohomologyAction
