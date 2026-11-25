/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenCounitModel
public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageSquareUnitNormalization

/-! # Composition normalization by derived units

Source: Stacks Project, Cohomology, Tags 08FE and 08BV.
(blueprint: lem-pc-derived-mayer-vietoris-open-composition-normalization).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry

/-- Determining equation of the concrete composite unit.
Source: Stacks Tag 0D5T (blueprint: def-pc-direct-image-composition-unit-source).
Proof: the defining equation of the comparison chosen by its unit equation. -/
private theorem schemeMVCompositionUnit_fac {A B D : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings A.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings B.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings D.toRingedSpace))]
    (s : A ⟶ B) (t : B ⟶ D)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings A.toRingedSpace))
      (ComplexShape.up ℤ)) :
    schemeMVCompositionUnit s t K ≫
        (schemeMVDirectImageComposition s t).hom.app (DerivedCategory.Qh.obj K) =
      (RingedSpace.moduleDirectImage t.toLRSHom.toShHom).rightDerivedFunctorUnit.app
          (((RingedSpace.moduleDirectImage s.toLRSHom.toShHom).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        (RingedSpace.moduleDirectImage t.toLRSHom.toShHom).rightDerivedFunctor.map
          ((RingedSpace.moduleDirectImage s.toLRSHom.toShHom).rightDerivedFunctorUnit.app K) := by
  unfold schemeMVCompositionUnit
  exact Classical.choose_spec (RingedSpace.exists_derivedModuleDirectImageComposition
    s.toLRSHom.toShHom t.toLRSHom.toShHom) K


variable (X Y : Scheme.{u}) (h : X ⟶ Y)
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ T : X.Opens, HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
  [∀ T : Y.Opens, HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
  (U : Y.Opens)

attribute [local instance 2000] schemeMVModuleAbelian

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The composition square commutes with the right-derived units, before any counit
is applied. This holds on every homotopy object, without a K-injectivity hypothesis.
Source: Stacks Tag 0D5T; Tag 08FE, composition on inverse-image opens.
Proof: apply the determining unit equation of each chosen composition comparison.
Transport the middle unit along the equality jX followed by h = g followed by jY.
Naturality of the right-derived unit identifies this transport with the image of
the underived open-composition identification. Cancel the comparison for g followed
by jY and reassociate. The result is the equality of the two pasted units displayed
below. No restriction functor or adjunction counit enters this computation.
(blueprint: lem-pc-derived-mayer-vietoris-open-composition-normalization). -/
theorem schemeMVOpenComposition_unit_normalization
    (β : schemeDerivedDirectImage (h ⁻¹ᵁ U).ι ⋙ schemeDerivedDirectImage h ≅
      schemeDerivedDirectImage (h ∣_ U) ⋙ schemeDerivedDirectImage U.ι)
    (hβ : β = (schemeMVDirectImageComposition (h ⁻¹ᵁ U).ι h).symm ≪≫
      eqToIso (congrArg schemeDerivedDirectImage (morphismRestrict_ι h U).symm) ≪≫
      schemeMVDirectImageComposition (h ∣_ U) U.ι)
    (K : HomotopyCategory
      (SheafOfModules.{u} (moduleRings (h ⁻¹ᵁ U).toScheme.toRingedSpace))
      (ComplexShape.up ℤ)) :
    let RX := RingedSpace.moduleDirectImage (h ⁻¹ᵁ U).ι.toLRSHom.toShHom
    let F := RingedSpace.moduleDirectImage h.toLRSHom.toShHom
    let G := RingedSpace.moduleDirectImage (h ∣_ U).toLRSHom.toShHom
    let RY := RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom
    F.rightDerivedFunctorUnit.app ((RX.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        F.rightDerivedFunctor.map (RX.rightDerivedFunctorUnit.app K) ≫
        β.hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map
          ((schemeMVHomotopyOpenComposition h U).hom.app K) ≫
        RY.rightDerivedFunctorUnit.app ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        RY.rightDerivedFunctor.map (G.rightDerivedFunctorUnit.app K) := by
  have hx := schemeMVCompositionUnit_fac (h ⁻¹ᵁ U).ι h K
  have hy := schemeMVCompositionUnit_fac (h ∣_ U) U.ι K
  have ht := schemeDirectImageSquare_single_unit_normalization.{u, w} X Y h U K
  dsimp only at ht
  dsimp only
  rw [hβ]
  simp only [← Category.assoc]
  conv_lhs => lhs; rw [← hx]
  conv_rhs => rw [Category.assoc]; rhs; rw [← hy]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc]
  conv_rhs => rw [← Category.assoc]
  exact congrArg (fun v ↦ v ≫
    (schemeMVDirectImageComposition (h ∣_ U) U.ι).hom.app (DerivedCategory.Qh.obj K)) ht

end AlgebraicGeometry
