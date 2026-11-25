/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenCounitModel

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
noncomputable section
namespace AlgebraicGeometry

/-- Section-element form of the ordinary open counit compatibility.
Source: Stacks Project, Cohomology of Sheaves, Tags 08FE and 08BV.
The proof expands the two comparison maps and counits on an open and an element;
functoriality of the presheaf restriction maps and thinness of opens identify the
resulting maps. (blueprint: lem-pc-mayer-vietoris-ordinary-open-counit-square-section-element) -/
theorem schemeMVOrdinaryOpenCounit_square_section_element
    (X Y : Scheme.{u}) (h : X ⟶ Y) (U : Y.Opens)
    (M : SheafOfModules.{u} (moduleRings (h ⁻¹ᵁ U).toScheme.toRingedSpace))
    (W : (U.toScheme : Scheme).Opensᵒᵖ)
    (x : (((schemeOpenRestriction Y U).obj
      ((RingedSpace.moduleDirectImage (h ⁻¹ᵁ U).ι.toLRSHom.toShHom ⋙
        RingedSpace.moduleDirectImage h.toLRSHom.toShHom).obj M)).val.obj W)) :
    (((schemeOpenRestriction Y U).map
        ((schemeMVUnderivedOpenComposition h U).hom.app M) ≫
        (schemeOpenModuleAdjunction Y U).counit.app
          ((RingedSpace.moduleDirectImage (h ∣_ U).toLRSHom.toShHom).obj M)).val.app W) x =
      (((schemeMVUnderivedOpenRestriction h U).hom.app
          ((RingedSpace.moduleDirectImage (h ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj M) ≫
        (RingedSpace.moduleDirectImage (h ∣_ U).toLRSHom.toShHom).map
          ((schemeOpenModuleAdjunction X (h ⁻¹ᵁ U)).counit.app M)).val.app W) x := by
  -- The comparison maps and counits are restrictions on the underlying sections.
  change M.val.presheaf.map _ (M.val.presheaf.map _ x) =
    M.val.presheaf.map _ (M.val.presheaf.map _ x)
  -- Combine the restrictions; the composite arrows agree since opens form a thin category.
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 1

end AlgebraicGeometry
