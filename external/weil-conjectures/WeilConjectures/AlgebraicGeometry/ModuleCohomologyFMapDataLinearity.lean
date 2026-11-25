/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapSemilinear

/-! Linearity of the map attached to explicit cohomology-map data.

Source: Stacks Project, Cohomology of Sheaves, Section 01F7, Remark 01FB.
(blueprint: lem-weil-pbc-module-cohomology-fmap-data-linearity).

The proof follows the module-linearity argument for the global-sections complexes,
transporting scalar actions through homology and the resolution comparison maps.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- The map produced by explicit resolution data is linear over global sections of `Y`.
Source: Stacks Project, Cohomology of Sheaves, Section 01F7, Remark 01FB.
(blueprint: lem-weil-pbc-module-cohomology-fmap-data-linearity).

The proof constructs the induced morphism on homology in the category of modules over
`O_Y(Y)`, using linearity of maps of sheaves, restriction of scalars along `h`, and
naturality of the canonical homology comparison isomorphisms. -/
theorem moduleCohomologyFMapData_map_linear
    {X Y : Scheme.{u}} {h : X ⟶ Y}
    {G : SheafOfModules.{u} Y.ringCatSheaf} {F : SheafOfModules.{u} X.ringCatSheaf}
    {φ : G ⟶ (pushforward h).obj F}
    (D : ModuleCohomologyFMapData h G F φ) (p : ℕ) :
    ∃ L : (Y.toRingedSpace.moduleCohomology p).obj G ⟶
          (ModuleCat.restrictScalars h.appTop.hom).obj
            ((X.toRingedSpace.moduleCohomology p).obj F),
      (forget₂ _ AddCommGrpCat).map L = D.map p := by
  obtain ⟨f, hf⟩ := D.map_semilinear p
  refine ⟨ModuleCat.semilinearMapAddEquiv h.appTop.hom _ _ f, ?_⟩
  ext x
  exact hf x

end AlgebraicGeometry.Scheme.Modules
