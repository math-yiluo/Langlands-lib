import Langlands.Shimura.Coefficients.ScalarExtension

/-! # Scalar extension of constant-module associated sheaves -/

noncomputable section

universe u v w

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Geometry Langlands.Geometry.EtaleCohomologyAction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section Site

variable {C : Type w} [Category.{v} C] (J : GrothendieckTopology C)
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
variable [HasSheafify J (ModuleCat.{u} R)] [HasSheafify J (ModuleCat.{u} S)]

/-- Sheafified tensor extension of a constant module is the extended constant sheaf. -/
def constantExtendScalarsIso :
    constantSheaf J (ModuleCat.{u} R) ⋙
        Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u, u, u} φ) ≅
      ModuleCat.extendScalars.{u, u, u} φ ⋙ constantSheaf J (ModuleCat.{u} S) :=
  Functor.isoWhiskerLeft (Functor.const Cᵒᵖ)
      (presheafToSheafCompComposeAndSheafifyIso J (ModuleCat.extendScalars.{u, u, u} φ)) ≪≫
    Functor.isoWhiskerRight (Functor.compConstIso _ _).symm (presheafToSheaf J _)

variable {G : Type u} [Group G]

/-- The constant tensor comparison transports the full coefficient group action. -/
def constantActionExtendScalarsIso :
    (constantSheaf J (ModuleCat.{u} R)).mapAction G ⋙
        (Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u, u, u} φ)).mapAction G ≅
      (ModuleCat.extendScalars.{u, u, u} φ).mapAction G ⋙
        (constantSheaf J (ModuleCat.{u} S)).mapAction G :=
  (Functor.mapActionComp G _ _).symm ≪≫
    Functor.mapActionCongr G (constantExtendScalarsIso J φ) ≪≫
      Functor.mapActionComp G _ _

@[simp]
theorem constantActionExtendScalarsIso_hom_hom (M : Action (ModuleCat.{u} R) G) :
    ((constantActionExtendScalarsIso J φ).hom.app M).hom =
      (constantExtendScalarsIso J φ).hom.app M.V := by
  simp [constantActionExtendScalarsIso]

@[simp]
theorem constantActionExtendScalarsIso_inv_hom (M : Action (ModuleCat.{u} R) G) :
    ((constantActionExtendScalarsIso J φ).inv.app M).hom =
      (constantExtendScalarsIso J φ).inv.app M.V := by
  simp [constantActionExtendScalarsIso]

end Site

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
variable (X : Scheme.{u}) {G : Type u} [Group G] (Y : Action X.Etale G)

/-- Canonical tensor comparison for associated sheaves of constant-module actions. -/
def constantAssociatedExtendScalarsComparison :
    constantAssociatedFunctor X.smallEtaleTopology Y ⋙ sheafExtendScalars φ X ⟶
      (ModuleCat.extendScalars.{u, u, u} φ).mapAction G ⋙
        constantAssociatedFunctor X.smallEtaleTopology Y :=
  Functor.whiskerLeft ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G)
      (associatedExtendScalarsComparison φ X Y) ≫
    Functor.whiskerRight (constantActionExtendScalarsIso X.smallEtaleTopology φ).hom
      (associatedFunctor X.smallEtaleTopology Y)

/-- The associated comparison is normalized by the actual tensor-sheaf unit. -/
@[reassoc]
theorem constantAssociatedExtendScalarsComparison_unit
    (M : Action (ModuleCat.{u} R) G) :
    (sheafExtensionUnit φ X).app ((constantAssociatedFunctor X.smallEtaleTopology Y).obj M) ≫
        (sheafRestrictScalars φ X).map
          ((constantAssociatedExtendScalarsComparison φ X Y).app M) =
      (associatedExtensionUnit φ X Y).app
          (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M) ≫
        (sheafRestrictScalars φ X).map ((associatedFunctor X.smallEtaleTopology Y).map
          ((constantActionExtendScalarsIso X.smallEtaleTopology φ).hom.app M)) := by
  dsimp only [constantAssociatedExtendScalarsComparison, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [Functor.map_comp, ← Category.assoc]
  erw [associatedExtendScalarsComparison_unit φ X Y
    (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M)]

/-- The tensor comparison respects the actual invariant inclusions on the cover. -/
@[reassoc]
theorem constantAssociatedExtendScalarsComparison_unit_inclusion
    (M : Action (ModuleCat.{u} R) G) :
    (sheafExtensionUnit φ X).app ((constantAssociatedFunctor X.smallEtaleTopology Y).obj M) ≫
        (sheafRestrictScalars φ X).map
          ((constantAssociatedExtendScalarsComparison φ X Y).app M ≫
            inclusion X.smallEtaleTopology Y
              (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} S)).mapAction G).obj
                (((ModuleCat.extendScalars.{u, u, u} φ).mapAction G).obj M))) =
      inclusion X.smallEtaleTopology Y
          (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M) ≫
        (productSheaf X.smallEtaleTopology Y.V).map
          ((sheafExtensionUnit φ X).app
              ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M.V) ≫
            (sheafRestrictScalars φ X).map
              ((constantExtendScalarsIso X.smallEtaleTopology φ).hom.app M.V)) := by
  rw [Functor.map_comp, ← Category.assoc,
    constantAssociatedExtendScalarsComparison_unit, Category.assoc, ← Functor.map_comp]
  erw [inclusion_natural X.smallEtaleTopology Y
    ((constantActionExtendScalarsIso X.smallEtaleTopology φ).hom.app M)]
  rw [Functor.map_comp, ← Category.assoc]
  erw [associatedExtensionUnit_inclusion φ X Y
    (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M)]
  rw [Category.assoc, constantActionExtendScalarsIso_hom_hom]
  change inclusion X.smallEtaleTopology Y
      (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M) ≫
    (productSheaf X.smallEtaleTopology Y.V).map
      ((sheafExtensionUnit φ X).app
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M.V)) ≫
    (productSheaf X.smallEtaleTopology Y.V).map
      ((sheafRestrictScalars φ X).map
        ((constantExtendScalarsIso X.smallEtaleTopology φ).hom.app M.V)) = _
  rw [← Functor.map_comp]

end Langlands.Shimura.Coefficients
