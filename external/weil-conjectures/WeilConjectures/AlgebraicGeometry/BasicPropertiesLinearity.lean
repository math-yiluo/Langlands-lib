/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapDataLinearity

/-! # Linearity property of module cohomology maps

Source: Stacks Project, Cohomology of Sheaves, Section 01F7, Remark 01FB.
(blueprint: lem-weil-pbc-module-cohomology-fmap-basic-linearity).
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
/-- Linearity property of the cohomology map induced by an h-map.
Source: Stacks Project, Cohomology of Sheaves, Tags 01F9, 01FA, 01FB;
Derived Categories, Tags 013P, 013S, 05TG.
(blueprint: lem-weil-pbc-module-cohomology-fmap-basic-linearity).

Proof (argument specialized from the parent node):
1. Choose the resolutions I, J, the auxiliary injective complex K, and the maps
   lambda and beta appearing in ModuleCohomologyFMapData. Evaluation of beta at Y
   gives a complex map of O_Y(Y)-modules. Evaluation of lambda is linear over the
   same ring, with sections of I on X regarded by restriction of scalars along h.appTop.
2. The sections comparison a is restriction along h^{-1}(Y) = X, so it too is linear
   after restricting scalars. Thus the composite mu = a followed by sections of lambda
   lifts to a map between complexes of O_Y(Y)-modules. Its underlying additive homology
   map is invertible by the pushforward-injectives sections quasi-isomorphism theorem.
3. Restriction of scalars and the forgetful functor preserve homology. Use their canonical
   homology comparisons to identify the homology of the restricted complex with the
   restricted homology of the original complex. The module homology map of mu is an
   isomorphism since the forgetful functor reflects isomorphisms.
4. Compose the module resolution comparison for J, homology of beta, the inverse of the
   module homology map of mu, and the restricted resolution comparison for I. Naturality
   of the forgetful homology comparisons identifies its underlying additive map with
   ModuleCohomologyFMapData.map. Apply this to the choices in moduleCohomologyFMap.
-/
theorem moduleCohomologyFMap_basic_linearity {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : SheafOfModules.{u} Y.ringCatSheaf} {F : SheafOfModules.{u} X.ringCatSheaf}
    (φ : G ⟶ (pushforward h).obj F) (p : ℕ) :
    ∃ L : (Y.toRingedSpace.moduleCohomology p).obj G ⟶
          (ModuleCat.restrictScalars h.appTop.hom).obj
            ((X.toRingedSpace.moduleCohomology p).obj F),
      (forget₂ _ AddCommGrpCat).map L = moduleCohomologyFMap h φ p := by
  let D := Classical.choice (moduleCohomologyFMapData_nonempty h G F φ)
  obtain ⟨L, hL⟩ := moduleCohomologyFMapData_map_linear D p
  exact ⟨L, hL.trans rfl⟩

end AlgebraicGeometry.Scheme.Modules
