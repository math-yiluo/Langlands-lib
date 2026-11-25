/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Matrix entries of the dual of a free sheaf

Source: Stacks Project, duality.tex, Tag 0BQZ, finite free Hom calculation.
(blueprint: lem-sc-free-sheaf-dual-transpose).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
private lemma coproduct_projection {X : Scheme.{u}} {I : Type u} [Finite I]
    [DecidableEq I] (i : I) :
    (biproduct.isoCoproduct (fun _ : I ↦ SheafOfModules.unit X.ringCatSheaf)).hom ≫
      Scheme.Modules.freeπ i =
    biproduct.π (fun _ : I ↦ SheafOfModules.unit X.ringCatSheaf) i := by
  apply biproduct.hom_ext'
  intro k
  classical
  simp [biproduct.isoCoproduct_hom, Scheme.Modules.freeπ, biproduct.ι_π]

private lemma unit_dual_conjugation {X : Scheme.{u}}
    (f : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (SheafOfModules.homObjUnitIso (R := X.toRingedSpace.sheaf)
      (SheafOfModules.unit X.ringCatSheaf)).inv ≫
      SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf) f (𝟙 _) ≫
      (SheafOfModules.homObjUnitIso (R := X.toRingedSpace.sheaf)
        (SheafOfModules.unit X.ringCatSheaf)).hom = f := by
  apply SheafOfModules.hom_ext
  ext V
  change (PresheafOfModules.homObjUnitInvApp
      (SheafOfModules.unit X.ringCatSheaf).val (1 : X.ringCatSheaf.obj.obj V)).app
      (op (Over.mk (𝟙 V.unop))) (f.val.app V (1 : X.ringCatSheaf.obj.obj V)) =
    f.val.app V (1 : X.ringCatSheaf.obj.obj V)
  rw [PresheafOfModules.homObjUnitInvApp_app_apply]
  let a : X.ringCatSheaf.obj.obj V := f.val.app V (1 : X.ringCatSheaf.obj.obj V)
  change a *
    X.ringCatSheaf.obj.map (𝟙 V) (1 : X.ringCatSheaf.obj.obj V) = a
  rw [X.ringCatSheaf.obj.map_id]
  exact mul_one _

set_option backward.isDefEq.respectTransparency false in
/-- The canonical finite free dual comparison transposes matrix components.
Source: Stacks Project, duality.tex, Tag 0BQZ, the finite free Hom calculation.
(blueprint: lem-sc-free-sheaf-dual-transpose).

Proof: The free sheaf is the finite coproduct of copies of the unit. Its internal
Hom is the product of the internal Homs of those copies. The canonical
homObjFreeUnitIso uses precisely this product decomposition and evaluation at
1 on each unit summand. Consequently the inverse comparison sends the i-th
free generator to the i-th coordinate functional. Precomposing that functional
with phi and evaluating on the j-th generator gives the (i,j) component of phi.
This is the asserted equality of endomorphisms of the unit: on every open,
both endomorphisms multiply by that same component. Equality of the values at
1 implies equality since the maps are linear. Empty index sets give no
components to check, and the calculation also holds over the zero ring. -/
theorem freeSheafDualTranspose_component {X : Scheme.{u}} {I J : Type u}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (phi : SheafOfModules.free (R := X.ringCatSheaf) J ⟶ SheafOfModules.free I)
    (i : I) (j : J) :
    SheafOfModules.ιFree i ≫ (SheafOfModules.homObjFreeUnitIso I).inv ≫
      SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf) phi
        (𝟙 (SheafOfModules.unit X.ringCatSheaf)) ≫
      (SheafOfModules.homObjFreeUnitIso J).hom ≫ Scheme.Modules.freeπ j =
    SheafOfModules.ιFree j ≫ phi ≫ Scheme.Modules.freeπ i  := by
  classical
  simp only [SheafOfModules.homObjFreeUnitIso, SheafOfModules.homObjFreeIso,
    Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.opMapBiproductIso, biproduct.uniqueUpToIso,
    biproduct.isoCoproduct_inv,
    SheafOfModules.ιFree, Category.assoc]
  simp only [Sigma.ι_comp_desc_assoc, biproduct.mapIso_inv, biproduct.ι_map_assoc,
    biproduct.ι_desc_assoc, Functor.opMapBicone_ι,
    biproduct.mapIso_hom, coproduct_projection]
  simp only [biproduct.map_π, biproduct.lift_π_assoc, Functor.opMapBicone_π]
  simp only [Iso.op_inv, Iso.op_hom]
  dsimp only [Functor.flip, SheafOfModules.homFunctor]
  simp only [SheafOfModules.homObjMap_comp_homObjMap_assoc, Category.comp_id]
  simp only [Quiver.Hom.unop_op, Category.assoc, biproduct.isoCoproduct_hom,
    biproduct.ι_desc_assoc]
  have hp :
      (biproduct.isoCoproduct (fun _ : I ↦ SheafOfModules.unit X.ringCatSheaf)).inv ≫
        biproduct.π (fun _ : I ↦ SheafOfModules.unit X.ringCatSheaf) i =
      Scheme.Modules.freeπ i := by
    rw [← coproduct_projection i]
    simp only [Iso.inv_hom_id_assoc]
  rw [hp]
  exact unit_dual_conjugation _

end AlgebraicGeometry
