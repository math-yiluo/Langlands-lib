/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedPresentation
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial

/-! # Transport of maps between square-zero tensor kernels

Source: Stacks Project, Tags 09MS, 01XC and 01F8.
(blueprint: lem-sc-tensor-boundary-kernel-map-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
universe u
attribute [local irreducible] RingedSpace.moduleCohomology
  moduleCohomologyEdgeMap moduleCohomologyFMap
  boundaryIdealKernelIso boundaryCoefficientDegreeIso
noncomputable section

/-- Identify the degree kernel with the pushforward of its coefficient module.
Source: Stacks Project, Tags 09MS and 08KS.
(blueprint: lem-sc-tensor-boundary-kernel-map-naturality).
The ideal-kernel isomorphism is characterized by its inclusion equation. The unit is
invertible by square-zero annihilation. All maps here are explicit composites. -/
def tensorBoundaryKernelPushforwardIso {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n e : ℕ) :
    kernel (tensorGradedUnit j (L.tensorPow (n * (e + 1)))) ≅
      (pushforward j).obj
        ((tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n) ⊗
          (((tensorPullback j).obj L).tensorPow n).tensorPow e) := by
  have := square_zero_ideal_tensor_unit_isIso j L hI (n * (e + 1))
  exact (boundaryIdealKernelIso j (L.tensorPow (n * (e + 1)))).symm ≪≫
    asIso ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
      (j.ker.toModules ⊗ L.tensorPow (n * (e + 1)))) ≪≫
    (pushforward j).mapIso (boundaryCoefficientDegreeIso j L n e)

/-- Transport an arbitrary coefficient morphism back to the degree kernels.
Source: Stacks Project, Tags 09MS and 08KS.
(blueprint: lem-sc-tensor-boundary-kernel-map-naturality). -/
def tensorBoundaryKernelMap {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n a b : ℕ)
    (v : (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n) ⊗
        (((tensorPullback j).obj L).tensorPow n).tensorPow a ⟶
      (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n) ⊗
        (((tensorPullback j).obj L).tensorPow n).tensorPow b) :
    kernel (tensorGradedUnit j (L.tensorPow (n * (a + 1)))) ⟶
      kernel (tensorGradedUnit j (L.tensorPow (n * (b + 1)))) :=
  (tensorBoundaryKernelPushforwardIso j L hI n a).hom ≫
    (pushforward j).map v ≫ (tensorBoundaryKernelPushforwardIso j L hI n b).inv

attribute [irreducible] tensorBoundaryKernelPushforwardIso tensorBoundaryKernelMap

private theorem edge_naturality {X Z : Scheme.{u}} (j : Z ⟶ X)
    {A B : Z.Modules} (v : A ⟶ B) :
    (forget₂ _ AddCommGrpCat.{u}).map
        ((RingedSpace.moduleCohomology X.toRingedSpace 1).map ((pushforward j).map v)) ≫
      moduleCohomologyEdgeMap j B 1 =
    moduleCohomologyEdgeMap j A 1 ≫
      (forget₂ _ AddCommGrpCat.{u}).map
        ((RingedSpace.moduleCohomology Z.toRingedSpace 1).map v) := by
  have hs := moduleCohomologyFMap_source_naturality j ((pushforward j).map v) (𝟙 _) 1
  have ht := moduleCohomologyFMap_target_naturality j v (𝟙 _) 1
  simpa only [moduleCohomologyEdgeMap, Category.comp_id, Category.id_comp] using
    hs.trans ht.symm

private theorem comparison_inv_eq {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n e : ℕ) :
    (boundaryCoefficientCohomologyIso j L hI n e).inv =
      (forget₂ _ AddCommGrpCat.{u}).map
          ((RingedSpace.moduleCohomology X.toRingedSpace 1).map
            (tensorBoundaryKernelPushforwardIso j L hI n e).hom) ≫
        moduleCohomologyEdgeMap j
          (show Z.Modules from (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n) ⊗
            (((tensorPullback j).obj L).tensorPow n).tensorPow e) 1 := by
  let HX := RingedSpace.moduleCohomology X.toRingedSpace 1 ⋙
    forget₂ _ AddCommGrpCat.{u}
  let HZ := RingedSpace.moduleCohomology Z.toRingedSpace 1 ⋙
    forget₂ _ AddCommGrpCat.{u}
  let Jd : X.Modules := j.ker.toModules ⊗ L.tensorPow (n * (e + 1))
  let A : Z.Modules := (tensorPullback j).obj Jd
  let B : Z.Modules := (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n) ⊗
    (((tensorPullback j).obj L).tensorPow n).tensorPow e
  let k := (boundaryIdealKernelIso j (L.tensorPow (n * (e + 1)))).inv
  let η := (Classical.choose (exists_tensorPullbackAdjunction j)).unit.app Jd
  let c := (boundaryCoefficientDegreeIso j L n e).hom
  change _ = HX.map (tensorBoundaryKernelPushforwardIso j L hI n e).hom ≫
    moduleCohomologyEdgeMap j B 1
  calc
    (boundaryCoefficientCohomologyIso j L hI n e).inv =
        HX.map k ≫ HX.map η ≫ moduleCohomologyEdgeMap j A 1 ≫ HZ.map c := by
      rfl
    _ = HX.map k ≫ HX.map η ≫
        HX.map ((pushforward j).map c) ≫ moduleCohomologyEdgeMap j B 1 :=
      congrArg (fun g ↦ HX.map k ≫ HX.map η ≫ g) (edge_naturality j c).symm
    _ = HX.map (k ≫ η ≫ (pushforward j).map c) ≫
        moduleCohomologyEdgeMap j B 1 := by
      simp only [HX.map_comp, Category.assoc]
    _ = HX.map (tensorBoundaryKernelPushforwardIso j L hI n e).hom ≫
        moduleCohomologyEdgeMap j B 1 := by
      apply congrArg (fun g ↦ HX.map g ≫ moduleCohomologyEdgeMap j B 1)
      simp only [tensorBoundaryKernelPushforwardIso, Iso.trans_hom, Iso.symm_hom,
        Functor.mapIso_hom, asIso_hom]
      rfl

attribute [local irreducible] boundaryCoefficientCohomologyIso

/-- The canonical coefficient comparisons intertwine every transported kernel map.
Source: Stacks Project, Tag 01XC (affine comparison), Tag 01F8 (functoriality),
and Tag 09MS (ideal and tensor-degree identifications).
(blueprint: lem-sc-tensor-boundary-kernel-map-naturality).
Proof: Write the inverse coefficient comparison as H of the kernel-to-pushforward
isomorphism followed by the edge map. This follows by expanding the canonical
comparison, functoriality of H, and naturality of the edge map for the tensor-degree
isomorphism. Apply edge naturality to v. Expand the transported map and cancel the
kernel-to-pushforward isomorphism of the target. Evaluating this commuting square
on w gives the assertion. No graded algebra, quotient action, or homogeneous section
is involved; a and b are arbitrary, including zero. -/
theorem tensorBoundaryKernelMap_naturality {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n a b : ℕ)
    (v : (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n) ⊗
        (((tensorPullback j).obj L).tensorPow n).tensorPow a ⟶
      (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n) ⊗
        (((tensorPullback j).obj L).tensorPow n).tensorPow b)
    :
    ((RingedSpace.moduleCohomology X.toRingedSpace 1 ⋙
      forget₂ _ AddCommGrpCat.{u}).map (tensorBoundaryKernelMap j L hI n a b v)) ≫
        (boundaryCoefficientCohomologyIso j L hI n b).inv =
      (boundaryCoefficientCohomologyIso j L hI n a).inv ≫
        (RingedSpace.moduleCohomology Z.toRingedSpace 1 ⋙
          forget₂ _ AddCommGrpCat.{u}).map v := by
  let HX := RingedSpace.moduleCohomology X.toRingedSpace 1 ⋙
    forget₂ _ AddCommGrpCat.{u}
  let HZ := RingedSpace.moduleCohomology Z.toRingedSpace 1 ⋙
    forget₂ _ AddCommGrpCat.{u}
  let A : Z.Modules := (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n) ⊗
    (((tensorPullback j).obj L).tensorPow n).tensorPow a
  let B : Z.Modules := (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n) ⊗
    (((tensorPullback j).obj L).tensorPow n).tensorPow b
  let ta := tensorBoundaryKernelPushforwardIso j L hI n a
  let tb := tensorBoundaryKernelPushforwardIso j L hI n b
  let m := tensorBoundaryKernelMap j L hI n a b v
  have hm : m ≫ tb.hom = ta.hom ≫ (pushforward j).map v := by
    simp only [m, tensorBoundaryKernelMap, ta, tb, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have hc : HX.map m ≫ (boundaryCoefficientCohomologyIso j L hI n b).inv =
      (boundaryCoefficientCohomologyIso j L hI n a).inv ≫ HZ.map v := by
    calc
      HX.map m ≫ (boundaryCoefficientCohomologyIso j L hI n b).inv =
          HX.map m ≫ (HX.map tb.hom ≫ moduleCohomologyEdgeMap j B 1) :=
        congrArg (fun g ↦ HX.map m ≫ g) (comparison_inv_eq j L hI n b)
      _ = HX.map (m ≫ tb.hom) ≫ moduleCohomologyEdgeMap j B 1 :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun g ↦ g ≫ moduleCohomologyEdgeMap j B 1)
            (HX.map_comp m tb.hom).symm)
      _ = HX.map (ta.hom ≫ (pushforward j).map v) ≫
          moduleCohomologyEdgeMap j B 1 :=
        congrArg (fun g ↦ HX.map g ≫ moduleCohomologyEdgeMap j B 1) hm
      _ = HX.map ta.hom ≫ (HX.map ((pushforward j).map v) ≫
          moduleCohomologyEdgeMap j B 1) :=
        (congrArg (fun g ↦ g ≫ moduleCohomologyEdgeMap j B 1)
          (HX.map_comp ta.hom ((pushforward j).map v))).trans (Category.assoc _ _ _)
      _ = HX.map ta.hom ≫ (moduleCohomologyEdgeMap j A 1 ≫ HZ.map v) :=
        congrArg (fun g ↦ HX.map ta.hom ≫ g) (edge_naturality j v)
      _ = (HX.map ta.hom ≫ moduleCohomologyEdgeMap j A 1) ≫ HZ.map v :=
        (Category.assoc _ _ _).symm
      _ = (boundaryCoefficientCohomologyIso j L hI n a).inv ≫ HZ.map v :=
        congrArg (fun g ↦ g ≫ HZ.map v) (comparison_inv_eq j L hI n a).symm
  exact hc

end
end AlgebraicGeometry.Scheme.Modules
