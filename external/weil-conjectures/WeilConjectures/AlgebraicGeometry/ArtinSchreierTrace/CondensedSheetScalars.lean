/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.SplitCondensedRegularProduct
import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
import all WeilConjectures.AlgebraicGeometry.PullbackScalar.PullbackScalar

/-! # Constant scalar compatibility of the sheet projections -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ArtinSchreierTrace

attribute [local implicit_reducible] condensedUnit
attribute [local implicit_reducible] CommMon.toMon
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  ProEtale.sheafMonoidalCategory ProEtale.sheafBraidedCategory
  ProEtale.sheafSymmetricCategory Mod.monoidalCategory Monoidal.induced

attribute [local irreducible] ProEtale.CondensedRing.monoidal_upperStar
  Mod.monoidal_extendScalars Functor.monoidal_mapMod

private instance pointColimits (X : Scheme.{u}) :
    PreservesColimits (ProEtale.upperStarFromPoint X) :=
  (ProEtale.pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1}
      (ProEtale.toSpecZ X))).leftAdjoint_preservesColimits

private instance pointAdditive (X : Scheme.{u}) :
    (ProEtale.upperStarFromPoint X).Additive := by
  have : PreservesBinaryBiproducts (ProEtale.upperStarFromPoint X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

private theorem pointEnd_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (a : MonObj.Γ Λ) :
    (Mod.regularEndRingHom
      (MonObj.Γ.mapFunctorMonoidHom (ProEtale.upperStarFromPoint X) a)).asHom.hom =
        (ProEtale.upperStarFromPoint X).map (Mod.regularEndRingHom a).asHom.hom := by
  have h := (ProEtale.upperStarFromPoint X).mapMod_map_regularEndRingHom Λ a
  exact (congrArg Mod.Hom.hom h).symm

-- Internal-module coefficient comparisons need additional kernel conversion.
private theorem pointEnd_pullback_unit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : MonObj.Γ Λ) :
    (ProEtale.CondensedRing.upperStar Λ f).map
        (Mod.regularEndRingHom
          (MonObj.Γ.mapFunctorMonoidHom (ProEtale.upperStarFromPoint Y) a)).asHom ≫
      (regularUnitIso Λ f).inv =
    (regularUnitIso Λ f).inv ≫
      (Mod.regularEndRingHom
        (MonObj.Γ.mapFunctorMonoidHom (ProEtale.upperStarFromPoint X) a)).asHom := by
  have he (Z : Scheme.{u}) :
      ProEtale.PullbackScalar.pointScalar Λ Z (Mod.regularEndRingHom a) =
        Mod.regularEndRingHom
          (MonObj.Γ.mapFunctorMonoidHom (ProEtale.upperStarFromPoint Z) a) := by
    apply End.ext
    apply Mod.hom_ext
    rw [ProEtale.PullbackScalar.pointScalar_hom, pointEnd_hom]
    rfl
  have h := ProEtale.PullbackScalar.pullback_unit_scalar Λ f (Mod.regularEndRingHom a)
  simp only [ProEtale.PullbackScalar.pullbackUnit, he] at h
  unfold regularUnitIso
  convert h using 1 <;> rfl

-- Internal-module coefficient comparisons need additional kernel conversion.
/-- Constant coefficient multiplication commutes with restriction to a sheet.
Source: blueprint lemma-artin-schreier-character-sheaf, weighted character averaging
(blueprint: lem-fd-as-sheet-scalars).

Proof: naturality of the counit and composition comparison moves the scalar
through stalkLowerStarProj. On regular modules the remaining pullback is the
same scalar: naturality of upperStarFromPointComp gives its coefficient square,
and the extension adjunction and unit comparison identify the scalar maps. -/
theorem sheetProjection_scalar
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y T : Scheme.{u}}
    (π : Y ⟶ X) (x : T ⟶ X) (t : T ⟶ Y) (w : t ≫ π = x)
    (a : MonObj.Γ Λ) :
    (ProEtale.CondensedRing.upperStar Λ x).map
        ((ProEtale.CondensedRing.lowerStar Λ π).map
          (Mod.regularEndRingHom
            (MonObj.Γ.mapFunctorMonoidHom (ProEtale.upperStarFromPoint Y) a)).asHom) ≫
      sheetProjection Λ π x t w =
    sheetProjection Λ π x t w ≫
      (Mod.regularEndRingHom
        (MonObj.Γ.mapFunctorMonoidHom (ProEtale.upperStarFromPoint T) a)).asHom := by
  simp only [sheetProjection, Category.assoc]
  erw [ProEtale.CondensedRing.stalkLowerStarProj_naturality_assoc]
  rw [pointEnd_pullback_unit]
  rfl

end AlgebraicGeometry.ArtinSchreierTrace
