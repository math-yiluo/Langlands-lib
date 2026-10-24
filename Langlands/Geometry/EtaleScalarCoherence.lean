import Langlands.Geometry.EtaleScalarRestriction

/-!
# Identity and composition for equivariant scalar restriction
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u t

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
variable (φ : R →+* A) (ψ : A →+* B) (χ : B →+* C)
variable (X : Scheme.{u})

/-- Restriction by the identity ring homomorphism is naturally the identity on sheaves. -/
def sheafRestrictScalarsIdIso :
    sheafRestrictScalars (RingHom.id R) X ≅ 𝟭 (EtaleDerivedSections.ModuleSheaf X R) :=
  NatIso.ofComponents
    (fun F =>
      { hom := .mk (Functor.whiskerLeft F.obj (ModuleCat.restrictScalarsId R).hom)
        inv := .mk (Functor.whiskerLeft F.obj (ModuleCat.restrictScalarsId R).inv)
        hom_inv_id := by ext U x; rfl
        inv_hom_id := by ext U x; rfl })
    (fun f => by ext U x; rfl)

/-- Restriction along a composite ring map is naturally successive restriction. -/
def sheafRestrictScalarsCompIso :
    sheafRestrictScalars (ψ.comp φ) X ≅
      sheafRestrictScalars ψ X ⋙ sheafRestrictScalars φ X :=
  NatIso.ofComponents
    (fun F =>
      { hom := .mk (Functor.whiskerLeft F.obj (ModuleCat.restrictScalarsComp φ ψ).hom)
        inv := .mk (Functor.whiskerLeft F.obj (ModuleCat.restrictScalarsComp φ ψ).inv)
        hom_inv_id := by ext U x; rfl
        inv_hom_id := by ext U x; rfl })
    (fun f => by ext U x; rfl)

/-- The identity sheaf comparison is the module comparison on each section. -/
@[simp] theorem sheafRestrictScalarsIdIso_hom_app
    (F : EtaleDerivedSections.ModuleSheaf X R) (U : X.Etaleᵒᵖ) :
    ((sheafRestrictScalarsIdIso X).hom.app F).hom.app U =
      (ModuleCat.restrictScalarsId R).hom.app (F.obj.obj U) := rfl

/-- The inverse identity comparison is the inverse module comparison on sections. -/
@[simp] theorem sheafRestrictScalarsIdIso_inv_app
    (F : EtaleDerivedSections.ModuleSheaf X R) (U : X.Etaleᵒᵖ) :
    ((sheafRestrictScalarsIdIso X).inv.app F).hom.app U =
      (ModuleCat.restrictScalarsId R).inv.app (F.obj.obj U) := rfl

/-- The composite sheaf comparison is the module comparison on each section. -/
@[simp] theorem sheafRestrictScalarsCompIso_hom_app
    (F : EtaleDerivedSections.ModuleSheaf X B) (U : X.Etaleᵒᵖ) :
    ((sheafRestrictScalarsCompIso φ ψ X).hom.app F).hom.app U =
      (ModuleCat.restrictScalarsComp φ ψ).hom.app (F.obj.obj U) := rfl

/-- The inverse composite comparison is the inverse module comparison on sections. -/
@[simp] theorem sheafRestrictScalarsCompIso_inv_app
    (F : EtaleDerivedSections.ModuleSheaf X B) (U : X.Etaleᵒᵖ) :
    ((sheafRestrictScalarsCompIso φ ψ X).inv.app F).hom.app U =
      (ModuleCat.restrictScalarsComp φ ψ).inv.app (F.obj.obj U) := rfl

/-- Splitting off the identity at the source ring and then removing it is identity. -/
theorem sheafRestrictScalarsCompIso_id_left
    (F : EtaleDerivedSections.ModuleSheaf X A) :
    (sheafRestrictScalarsCompIso (RingHom.id R) φ X).hom.app F ≫
        (sheafRestrictScalarsIdIso X).hom.app ((sheafRestrictScalars φ X).obj F) =
      𝟙 ((sheafRestrictScalars φ X).obj F) := by
  ext U x
  rfl

/-- Splitting off the identity at the target ring and then removing it is identity. -/
theorem sheafRestrictScalarsCompIso_id_right
    (F : EtaleDerivedSections.ModuleSheaf X A) :
    (sheafRestrictScalarsCompIso φ (RingHom.id A) X).hom.app F ≫
        (sheafRestrictScalars φ X).map ((sheafRestrictScalarsIdIso X).hom.app F) =
      𝟙 ((sheafRestrictScalars φ X).obj F) := by
  ext U x
  rfl

/-- The two ways of splitting a triple ring composite give the same sheaf map. -/
theorem sheafRestrictScalarsCompIso_assoc
    (F : EtaleDerivedSections.ModuleSheaf X C) :
    (sheafRestrictScalarsCompIso φ (χ.comp ψ) X).hom.app F ≫
        (sheafRestrictScalars φ X).map ((sheafRestrictScalarsCompIso ψ χ X).hom.app F) =
      (sheafRestrictScalarsCompIso (ψ.comp φ) χ X).hom.app F ≫
        (sheafRestrictScalarsCompIso φ ψ X).hom.app ((sheafRestrictScalars χ X).obj F) := by
  ext U x
  rfl

variable {X} {G : Type t} [Group G] (ρ : G →* (Aut X)ᵐᵒᵖ)

/-- The identity scalar comparison respects the geometric group action. -/
def scalarRestrictionIdIso :
    scalarRestrictionFunctor (RingHom.id R) ρ ≅ 𝟭 (EquivariantSheaf R ρ) :=
  NatIso.ofComponents
    (fun F => TranslationAction.Equivariant.mkIso
      ((sheafRestrictScalarsIdIso X).app F.obj) (fun g => by ext U x; rfl))
    (fun f => by apply TranslationAction.Equivariant.Hom.ext; ext U x; rfl)

/-- The composite scalar comparison respects the geometric group action. -/
def scalarRestrictionCompIso :
    scalarRestrictionFunctor (ψ.comp φ) ρ ≅
      scalarRestrictionFunctor ψ ρ ⋙ scalarRestrictionFunctor φ ρ :=
  NatIso.ofComponents
    (fun F => TranslationAction.Equivariant.mkIso
      ((sheafRestrictScalarsCompIso φ ψ X).app F.obj) (fun g => by ext U x; rfl))
    (fun f => by apply TranslationAction.Equivariant.Hom.ext; ext U x; rfl)

/-- Forgetting equivariance recovers the identity sheaf comparison. -/
@[simp] theorem scalarRestrictionIdIso_hom_app_hom (F : EquivariantSheaf R ρ) :
    ((scalarRestrictionIdIso ρ).hom.app F).hom =
      (sheafRestrictScalarsIdIso X).hom.app F.obj := rfl

/-- The inverse equivariant identity comparison has the expected sheaf map. -/
@[simp] theorem scalarRestrictionIdIso_inv_app_hom (F : EquivariantSheaf R ρ) :
    ((scalarRestrictionIdIso ρ).inv.app F).hom =
      (sheafRestrictScalarsIdIso X).inv.app F.obj := rfl

/-- Forgetting equivariance recovers the composite sheaf comparison. -/
@[simp] theorem scalarRestrictionCompIso_hom_app_hom (F : EquivariantSheaf B ρ) :
    ((scalarRestrictionCompIso φ ψ ρ).hom.app F).hom =
      (sheafRestrictScalarsCompIso φ ψ X).hom.app F.obj := rfl

/-- The inverse equivariant composite comparison has the expected sheaf map. -/
@[simp] theorem scalarRestrictionCompIso_inv_app_hom (F : EquivariantSheaf B ρ) :
    ((scalarRestrictionCompIso φ ψ ρ).inv.app F).hom =
      (sheafRestrictScalarsCompIso φ ψ X).inv.app F.obj := rfl

/-- The source-ring unit law holds in the equivariant sheaf category. -/
theorem scalarRestrictionCompIso_id_left (F : EquivariantSheaf A ρ) :
    (scalarRestrictionCompIso (RingHom.id R) φ ρ).hom.app F ≫
        (scalarRestrictionIdIso ρ).hom.app ((scalarRestrictionFunctor φ ρ).obj F) =
      𝟙 ((scalarRestrictionFunctor φ ρ).obj F) := by
  apply TranslationAction.Equivariant.Hom.ext
  exact sheafRestrictScalarsCompIso_id_left φ X F.obj

/-- The target-ring unit law holds in the equivariant sheaf category. -/
theorem scalarRestrictionCompIso_id_right (F : EquivariantSheaf A ρ) :
    (scalarRestrictionCompIso φ (RingHom.id A) ρ).hom.app F ≫
        (scalarRestrictionFunctor φ ρ).map ((scalarRestrictionIdIso ρ).hom.app F) =
      𝟙 ((scalarRestrictionFunctor φ ρ).obj F) := by
  apply TranslationAction.Equivariant.Hom.ext
  exact sheafRestrictScalarsCompIso_id_right φ X F.obj

/-- Associativity of composite scalar restriction holds with geometric equivariance. -/
theorem scalarRestrictionCompIso_assoc (F : EquivariantSheaf C ρ) :
    (scalarRestrictionCompIso φ (χ.comp ψ) ρ).hom.app F ≫
        (scalarRestrictionFunctor φ ρ).map ((scalarRestrictionCompIso ψ χ ρ).hom.app F) =
      (scalarRestrictionCompIso (ψ.comp φ) χ ρ).hom.app F ≫
        (scalarRestrictionCompIso φ ψ ρ).hom.app ((scalarRestrictionFunctor χ ρ).obj F) := by
  apply TranslationAction.Equivariant.Hom.ext
  exact sheafRestrictScalarsCompIso_assoc φ ψ χ X F.obj

end Langlands.Geometry.EtaleCohomologyAction
