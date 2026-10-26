import Langlands.Shimura.Coefficients.ConstantScalarRestriction
import Langlands.Shimura.Coefficients.ConstantScalarExtension

/-! # Compatibility of constant scalar comparisons with the tensor unit -/

noncomputable section

universe u v w

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section Site

variable {C : Type w} [Category.{v} C] (J : GrothendieckTopology C)
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
variable [HasSheafify J (ModuleCat.{u} R)] [HasSheafify J (ModuleCat.{u} S)]

/-- The inverse constant tensor comparison is induced by the sheafification unit. -/
theorem constantExtendScalarsIso_inv_hom (M : ModuleCat.{u} R) :
    ((constantExtendScalarsIso J φ).inv.app M).hom =
      sheafifyMap J (Functor.constComp Cᵒᵖ M (ModuleCat.extendScalars.{u, u, u} φ)).inv ≫
        sheafifyMap J (Functor.whiskerRight
          (toSheafify J ((Functor.const Cᵒᵖ).obj M)) (ModuleCat.extendScalars.{u, u, u} φ)) := by
  rfl

/-- The constant restriction comparison carries the presheaf sheafification unit. -/
@[reassoc]
theorem constantRestrictScalarsIso_toSheafify (M : ModuleCat.{u} S) :
    Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M))
        (ModuleCat.restrictScalars.{u} φ) ≫
      ((constantRestrictScalarsIso J φ).hom.app M).hom =
        (Functor.constComp Cᵒᵖ M (ModuleCat.restrictScalars.{u} φ)).hom ≫
          toSheafify J ((Functor.const Cᵒᵖ).obj
            ((ModuleCat.restrictScalars.{u} φ).obj M)) := by
  rw [constantRestrictScalarsIso, constantCommuteCompose_hom_app_hom,
    ← Category.assoc, sheafComposeIso_inv_fac, ← toSheafify_naturality]

/-- The constant extension comparison carries the tensor presheaf sheafification unit. -/
@[reassoc]
theorem constantExtendScalarsIso_toSheafify (M : ModuleCat.{u} R) :
    Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M))
        (ModuleCat.extendScalars.{u, u, u} φ) ≫
      toSheafify J (sheafify J ((Functor.const Cᵒᵖ).obj M) ⋙
        ModuleCat.extendScalars.{u, u, u} φ) ≫
      ((constantExtendScalarsIso J φ).hom.app M).hom =
        (Functor.constComp Cᵒᵖ M (ModuleCat.extendScalars.{u, u, u} φ)).hom ≫
          toSheafify J ((Functor.const Cᵒᵖ).obj
            ((ModuleCat.extendScalars.{u, u, u} φ).obj M)) := by
  apply (cancel_mono ((constantExtendScalarsIso J φ).inv.app M).hom).mp
  have hc := congrArg (fun f => f.hom) ((constantExtendScalarsIso J φ).hom_inv_id_app M)
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.id_hom] at hc
  simp only [Category.assoc]
  rw [hc]
  erw [Category.comp_id]
  rw [constantExtendScalarsIso_inv_hom]
  erw [← toSheafify_naturality_assoc, ← Category.assoc, Iso.hom_inv_id,
    Category.id_comp, ← toSheafify_naturality]

/-- Constant scalar extension and restriction transport the module tensor unit. -/
@[reassoc]
theorem constantScalarChange_unit (M : ModuleCat.{u} R) :
    (CategoryTheory.Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ)).unit.app
        ((constantSheaf J (ModuleCat.{u} R)).obj M) ≫
      (sheafCompose J (ModuleCat.restrictScalars.{u} φ)).map
        ((constantExtendScalarsIso J φ).hom.app M) ≫
      (constantRestrictScalarsIso J φ).hom.app ((ModuleCat.extendScalars.{u, u, u} φ).obj M) =
        (constantSheaf J (ModuleCat.{u} R)).map
          ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).unit.app M) := by
  apply CategoryTheory.Sheaf.hom_ext
  change ((CategoryTheory.Sheaf.adjunction J
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ)).unit.app
        ((constantSheaf J (ModuleCat.{u} R)).obj M)).hom ≫
      Functor.whiskerRight ((constantExtendScalarsIso J φ).hom.app M).hom
        (ModuleCat.restrictScalars.{u} φ) ≫
      ((constantRestrictScalarsIso J φ).hom.app
        ((ModuleCat.extendScalars.{u, u, u} φ).obj M)).hom =
      sheafifyMap J ((Functor.const Cᵒᵖ).map
        ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).unit.app M))
  rw [CategoryTheory.Sheaf.adjunction_unit_app_hom]
  apply sheafify_hom_ext J _ _
    ((constantSheaf J (ModuleCat.{u} R)).obj
      ((ModuleCat.restrictScalars.{u} φ).obj ((ModuleCat.extendScalars.{u, u, u} φ).obj M))).property
  have hη := ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).whiskerRight Cᵒᵖ).unit.naturality
    (toSheafify J ((Functor.const Cᵒᵖ).obj M))
  simp only [Functor.id_map, Functor.comp_map] at hη
  simp only [Category.assoc]
  rw [← Category.assoc (toSheafify J ((Functor.const Cᵒᵖ).obj M))]
  erw [hη]
  simp only [Category.assoc]
  change ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).whiskerRight Cᵒᵖ).unit.app
      ((Functor.const Cᵒᵖ).obj M) ≫
    Functor.whiskerRight (Functor.whiskerRight
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)) (ModuleCat.extendScalars.{u, u, u} φ))
      (ModuleCat.restrictScalars.{u} φ) ≫
    Functor.whiskerRight (toSheafify J (sheafify J ((Functor.const Cᵒᵖ).obj M) ⋙
      ModuleCat.extendScalars.{u, u, u} φ)) (ModuleCat.restrictScalars.{u} φ) ≫
    Functor.whiskerRight ((constantExtendScalarsIso J φ).hom.app M).hom
      (ModuleCat.restrictScalars.{u} φ) ≫
    ((constantRestrictScalarsIso J φ).hom.app
      ((ModuleCat.extendScalars.{u, u, u} φ).obj M)).hom = _
  rw [← Functor.whiskerRight_comp_assoc, ← Functor.whiskerRight_comp_assoc]
  erw [Category.assoc]
  erw [constantExtendScalarsIso_toSheafify J φ M]
  rw [Functor.whiskerRight_comp]
  simp only [Category.assoc]
  erw [constantRestrictScalarsIso_toSheafify J φ
    ((ModuleCat.extendScalars.{u, u, u} φ).obj M)]
  rw [← toSheafify_naturality]
  simp only [← Category.assoc]
  congr 1

end Site

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
variable {G : Type u} [Group G]

/-- The module tensor unit as a natural equivariant coefficient map. -/
def moduleExtensionActionUnit :
    𝟭 (Action (ModuleCat.{u} R) G) ⟶
      (ModuleCat.extendScalars.{u, u, u} φ).mapAction G ⋙
        (ModuleCat.restrictScalars.{u} φ).mapAction G where
  app M :=
    { hom := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).unit.app M.V
      comm g := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).unit.naturality (M.ρ g) }
  naturality {M N} f := by
    apply Action.hom_injective
    exact (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).unit.naturality f.hom

open AlgebraicGeometry
open Langlands.Geometry Langlands.Geometry.EtaleCohomologyAction

variable (X : Scheme.{u}) (Y : Action X.Etale G)

/-- The associated constant comparisons transport the actual module tensor unit. -/
@[reassoc]
theorem constantAssociatedScalarChange_unit (M : Action (ModuleCat.{u} R) G) :
    (sheafExtensionUnit φ X).app ((constantAssociatedFunctor X.smallEtaleTopology Y).obj M) ≫
      (sheafRestrictScalars φ X).map
        ((constantAssociatedExtendScalarsComparison φ X Y).app M) ≫
      (constantAssociatedRestrictScalarsIso X.smallEtaleTopology φ Y).hom.app
        (((ModuleCat.extendScalars.{u, u, u} φ).mapAction G).obj M) =
      (constantAssociatedFunctor X.smallEtaleTopology Y).map
        ((moduleExtensionActionUnit φ).app M) := by
  apply hom_ext X.smallEtaleTopology Y
  simp only [Category.assoc]
  erw [constantAssociatedRestrictScalarsIso_hom_inclusion X.smallEtaleTopology φ Y
    (((ModuleCat.extendScalars.{u, u, u} φ).mapAction G).obj M)]
  erw [← Functor.map_comp_assoc]
  rw [← Category.assoc]
  erw [constantAssociatedExtendScalarsComparison_unit_inclusion φ X Y M]
  rw [Category.assoc, ← Functor.map_comp]
  change inclusion X.smallEtaleTopology Y
      (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M) ≫
    (productSheaf X.smallEtaleTopology Y.V).map
      ((CategoryTheory.Sheaf.adjunction X.smallEtaleTopology
        (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ)).unit.app
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M.V) ≫
        (sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u} φ)).map
          ((constantExtendScalarsIso X.smallEtaleTopology φ).hom.app M.V) ≫
        (constantRestrictScalarsIso X.smallEtaleTopology φ).hom.app
          ((ModuleCat.extendScalars.{u, u, u} φ).obj M.V)) = _
  rw [constantScalarChange_unit X.smallEtaleTopology φ M.V]
  exact (inclusion_natural X.smallEtaleTopology Y
    (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).map
      ((moduleExtensionActionUnit φ).app M))).symm

end Langlands.Shimura.Coefficients
