/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarAbelianExtFactorization
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf

/-! # Scalar structure coefficient has the original structure-sheaf adjunct

Source: Stacks Project, Tags 0096 and 01F7.
(blueprint: new-sc-scalar-structure-coefficient-adjunct).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme
open Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Sheaf.monoidalCategory

/-- Scalar structure coefficient has the original structure-sheaf adjunct.
Source: Stacks Project, Tags 0096 and 01F7.
(blueprint: new-sc-scalar-structure-coefficient-adjunct).

Proof: Apply naturality on the target of the scalar inverse-image adjunction.
The characterization of scalarPullbackCoefficient says sectionwise that its
adjunct is the unit of the tensor pullback adjunction. After postcomposition by
tensorPullbackObjUnitToUnit, the second equation of
tensorPullbackObjUnitToUnit_isIso identifies this composite with the structure
sheaf map. Forgetting the scalar action changes neither sections nor maps.
Sheaf-map extensionality proves the result. No stalk, nonempty-open, or
characteristic assumption enters this calculation. -/
theorem scalar_structure_coefficient_adjunct (k : Type u) [Field k] {X Y : Scheme.{u}} (f : X ⟶
    Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k)) (a : Y ⟶ X) (h : a ≫ f = g) :
    (scalarAbelianForget k X).map ((((Opens.map a.base).sheafAdjunctionContinuous (ModuleCat.{u}
    k) _ _).homEquiv _ _) (scalarPullbackCoefficient f g a h (SheafOfModules.unit
    X.ringCatSheaf) ≫ scalarHom g (tensorPullbackObjUnitToUnit a))) = (show structureSheafAb X ⟶
    ((Opens.map a.base).sheafPushforwardContinuous AddCommGrpCat.{u} (Opens.grothendieckTopology
    X) (Opens.grothendieckTopology Y)).obj (structureSheafAb Y) from ⟨Functor.whiskerRight a.c
    (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u})⟩) := by
  unfold scalarPullbackCoefficient
  let adj := (Opens.map a.base).sheafAdjunctionContinuous (ModuleCat.{u} k)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  have hj := Classical.choose_spec
    (exists_scalarPullbackCoefficient f g a h (SheafOfModules.unit X.ringCatSheaf))
  rw [Adjunction.homEquiv_naturality_right]
  apply Sheaf.hom_ext
  ext U s
  change (tensorPullbackObjUnitToUnit a).val.app ((Opens.map a.base).op.obj U)
    (((adj.homEquiv _ _) (Classical.choose (exists_scalarPullbackCoefficient f g a h
      (SheafOfModules.unit X.ringCatSheaf)))).hom.app U s) = _
  rw [hj U.unop s]
  have ht := (tensorPullbackObjUnitToUnit_isIso a).2
  exact congrArg (fun t ↦ (t.val.app U).hom s) ht

end AlgebraicGeometry.Scheme
