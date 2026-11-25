/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageSectionPresheaf
import all WeilConjectures.AlgebraicGeometry.Section.SectionCohomologyCycleFormula

/-! # The ordinary local class on cycles

## References

* Stacks Project, Cohomology, Tag 01E4
* Stacks Project, Tags 01E4 and 0BKJ
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry
open Scheme.Modules

/-- The ordinary abelian sheafification class sends cycles to their module cohomology
classes through the canonical kernel comparison.
-/
theorem ordinaryLocalClass_cycles {Y : RingedSpace.{u}}
    (I : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ) (q : ℤ) :
    let F := RingedSpace.localAbelianSections Y
    let U := sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
    let P := (I.sc q).map F
    let k := (P.isoCyclesOfIsLimit
      (KernelFork.mapIsLimit _ (I.sc q).cyclesIsKernel F)).inv
    P.homologyπ ≫
        (sheafificationAdjunction (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).unit.app
          P.homology ≫
        U.map (RingedSpace.localSectionComplexSheafificationIso Y q I).hom =
      k ≫ F.map (I.sc q).homologyπ := by
  dsimp only
  let T := SheafOfModules.toSheaf.{u} (moduleRings Y)
  let U := sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
  let S := presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
  let F := RingedSpace.localAbelianSections Y
  let A := (I.sc q).map T
  let P := (I.sc q).map F
  let k := (P.isoCyclesOfIsLimit
    (KernelFork.mapIsLimit _ (I.sc q).cyclesIsKernel F)).inv
  let k' := ((A.map U).isoCyclesOfIsLimit
    (KernelFork.mapIsLimit _ A.cyclesIsKernel U)).inv
  let c := (sheafificationAdjunction (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
  have hc : (RingedSpace.localSectionComplexSheafificationIso Y q I).hom =
      (((A.map U).mapHomologyIso S).inv ≫
        ShortComplex.homologyMap (A.mapNatTrans c.counit)) ≫
        ((I.sc q).mapHomologyIso T).hom := by
    simp only [RingedSpace.localSectionComplexSheafificationIso,
      Functor.mapHomologicalComplexHomologyIso, HomologicalComplex.homologyFunctorIso,
      Functor.mapHomologicalComplexCompShortComplexFunctorIso,
      ShortComplex.homologyFunctorIso, T, U, S, A, c, Iso.app_hom,
      Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Iso.refl_hom, Iso.refl_inv,
      NatTrans.comp_app, NatTrans.id_app, NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc]
    erw [CategoryTheory.Functor.map_id, Category.comp_id,
      Category.id_comp, Category.id_comp]
  have h := adjoint_homology_comparison_cycles S U c A
  dsimp only at h
  change P.homologyπ ≫ c.unit.app P.homology ≫ U.map _ =
    k ≫ F.map (I.sc q).homologyπ
  rw [c.homEquiv_unit] at h
  rw [hc, U.map_comp]
  erw [reassoc_of% h]
  erw [← U.map_comp, homologyπ_mapHomologyIso_hom, U.map_comp]
  have hk : k' ≫ U.map ((I.sc q).mapCyclesIso T).hom = k := by
    apply (cancel_mono (F.map (I.sc q).iCycles)).1
    change (k' ≫ U.map ((I.sc q).mapCyclesIso T).hom) ≫
      U.map (T.map (I.sc q).iCycles) = _
    rw [Category.assoc, ← U.map_comp, ShortComplex.mapCyclesIso_hom_iCycles]
    rw [show k' ≫ U.map A.iCycles = P.iCycles from
      (A.map U).isoCyclesOfIsLimit_inv_ι _]
    exact (P.isoCyclesOfIsLimit_inv_ι _).symm
  change k' ≫ U.map ((I.sc q).mapCyclesIso T).hom ≫
    U.map (T.map (I.sc q).homologyπ) = _
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun l ↦ l ≫ U.map (T.map (I.sc q).homologyπ)) hk)

end AlgebraicGeometry
