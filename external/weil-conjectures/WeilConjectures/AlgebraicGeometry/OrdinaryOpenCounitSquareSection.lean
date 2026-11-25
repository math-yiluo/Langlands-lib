/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenCounitModel
import WeilConjectures.AlgebraicGeometry.OrdinaryOpenCounitSquareSectionElement

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
noncomputable section
namespace AlgebraicGeometry

/-- Sectionwise form of the ordinary open counit compatibility.
Source: the sectionwise calculation in Stacks Tags 08FE and 08BV.
(blueprint: lem-pc-mayer-vietoris-ordinary-open-counit-square-section) -/
theorem schemeMVOrdinaryOpenCounit_square_app
    (X Y : Scheme.{u}) (h : X ⟶ Y) (U : Y.Opens)
    (M : SheafOfModules.{u} (moduleRings (h ⁻¹ᵁ U).toScheme.toRingedSpace))
    (W : (U.toScheme : Scheme).Opensᵒᵖ) :
    (((schemeOpenRestriction Y U).map
        ((schemeMVUnderivedOpenComposition h U).hom.app M) ≫
        (schemeOpenModuleAdjunction Y U).counit.app
          ((RingedSpace.moduleDirectImage (h ∣_ U).toLRSHom.toShHom).obj M)).val.app W) =
      (((schemeMVUnderivedOpenRestriction h U).hom.app
          ((RingedSpace.moduleDirectImage (h ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj M) ≫
        (RingedSpace.moduleDirectImage (h ∣_ U).toLRSHom.toShHom).map
          ((schemeOpenModuleAdjunction X (h ⁻¹ᵁ U)).counit.app M)).val.app W) := by
  ext x
  exact schemeMVOrdinaryOpenCounit_square_section_element X Y h U M W x

end AlgebraicGeometry
