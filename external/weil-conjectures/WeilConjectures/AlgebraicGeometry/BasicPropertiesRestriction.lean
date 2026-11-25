/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.RestrictionNaturality

/-! # Restriction property of module cohomology maps

Source: Stacks Project, Cohomology of Sheaves, Section 01F7, Remark 01FB.
(blueprint: lem-weil-pbc-module-cohomology-fmap-basic-restriction).
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
/-- Restriction property of the cohomology map induced by an h-map.
Source: Stacks Project, Cohomology of Sheaves, Tags 01F9, 01FA, 01FB;
Derived Categories, Tags 013P, 013S, 05TG.
(blueprint: lem-weil-pbc-module-cohomology-fmap-basic-restriction).

Proof:
1. Restriction and tensor pullback are left adjoint to the same pushforward.
   Adjunction.leftAdjointUniq gives their canonical isomorphism kappa.
2. Apply moduleCohomologyFMap_target_iso_naturality to kappa at G and the
   restriction unit. This rewrites the left side as the cohomology map of the
   restriction unit followed by pushforward of kappa.hom.
3. Adjunction.unit_leftAdjointUniq_hom_app identifies that composite with
   the unit of the chosen tensor-pullback adjunction, giving the right side.
-/
theorem moduleCohomologyFMap_basic_restriction {Y : Scheme.{u}}
    (G : SheafOfModules.{u} Y.ringCatSheaf) (p : ℕ) :
    ∀ (U : Y.Opens),
      ∃ κ : (restrictFunctor U.ι).obj G ≅ (tensorPullback U.ι).obj G,
        moduleCohomologyFMap U.ι ((restrictAdjunction U.ι).unit.app G) p ≫
            (forget₂ _ AddCommGrpCat).map
              (((U : Scheme).toRingedSpace.moduleCohomology p).map κ.hom) =
          moduleCohomologyFMap U.ι
            ((Classical.choose (exists_tensorPullbackAdjunction U.ι)).unit.app G) p := by
  intro U
  let adjR := restrictAdjunction U.ι
  let adjT := Classical.choose (exists_tensorPullbackAdjunction U.ι)
  let κ : (restrictFunctor U.ι) ≅ (tensorPullback U.ι) :=
    Adjunction.leftAdjointUniq adjR adjT
  refine ⟨κ.app G, ?_⟩
  apply (moduleCohomologyFMap_target_iso_naturality U.ι
    ((restrictAdjunction U.ι).unit.app G) (κ.app G) p).trans
  congr 2
  exact Adjunction.unit_leftAdjointUniq_hom_app adjR adjT G

end AlgebraicGeometry.Scheme.Modules
