/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-! # The explicit quotient of affine residue cycles by residue boundaries

Source: Stacks Project, Section 12.13, Tag 010V; Mathlib's additive quotient API.
(blueprint: lem-sc-affine-residue-cycle-class-quotient)
(blueprint: lem-sc-affine-residue-cycle-homology-map)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

noncomputable section

variable (W : Scheme.{v}) (U : W.Opens) (p : Ideal Γ(W, U)) [p.IsPrime]

/-- Evaluation at the top of the localized site, followed by residue extension.
(blueprint: lem-sc-affine-residue-cycle-class-quotient)
-/
abbrev affineResidueTerm
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) (j : ℤ) :=
  p.ResidueField ⊗[Γ(W, U)] (K.X j).val.obj (.op (Over.mk (𝟙 U)))

/-- The actual residue differential; no model or witness is chosen.
(blueprint: lem-sc-affine-residue-cycle-class-quotient)
-/
abbrev affineResidueDifferential
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) (i j : ℤ) :
    affineResidueTerm W U p K i →ₗ[p.ResidueField] affineResidueTerm W U p K j :=
  (show (K.X i).val.obj (.op (Over.mk (𝟙 U))) →ₗ[Γ(W, U)]
    (K.X j).val.obj (.op (Over.mk (𝟙 U))) from
      ((K.d i j).val.app (.op (Over.mk (𝟙 U)))).hom).baseChange p.ResidueField

/-- Degree-one residue cycles.
(blueprint: lem-sc-affine-residue-cycle-class-quotient)
-/
abbrev affineResidueCycles
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) :=
  LinearMap.ker (affineResidueDifferential W U p K 1 2)

/-- Incoming residue boundaries, viewed as an additive subgroup of cycles.
(blueprint: lem-sc-affine-residue-cycle-class-quotient)
-/
def affineResidueBoundaries
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) :
    AddSubgroup (affineResidueCycles W U p K) :=
  (affineResidueDifferential W U p K 0 1).range.toAddSubgroup.comap
    (affineResidueCycles W U p K).subtype.toAddMonoidHom

/-- The concrete degree-one homology quotient.
(blueprint: lem-sc-affine-residue-cycle-class-quotient)
-/
abbrev affineResidueCycleHomology
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) :=
  affineResidueCycles W U p K ⧸ affineResidueBoundaries W U p K

/-- The canonical cycle-class map.
(blueprint: lem-sc-affine-residue-cycle-class-quotient)
-/
def affineResidueCycleClass
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) :
    affineResidueCycles W U p K →+ affineResidueCycleHomology W U p K :=
  QuotientAddGroup.mk' (affineResidueBoundaries W U p K)

/-- The residue cycle-class map is onto and its kernel is precisely incoming boundaries.
Source: Mathlib `QuotientAddGroup.mk'_surjective` and `QuotientAddGroup.eq_zero_iff`;
Stacks Project, Section 12.13, Tag 010V (homology as cycles modulo boundaries).
(blueprint: lem-sc-affine-residue-cycle-class-quotient)

Proof: The homology group is constructed as the additive quotient of the kernel
of the outgoing differential by the inverse image of the range of the incoming
differential under the cycle inclusion. The quotient projection is surjective.
Its class is zero exactly when the included cycle belongs to that range, which
means exactly that it is the incoming differential of some degree-zero element.
This construction retains nonzero boundaries and also handles the zero complex. -/
theorem affineResidueCycleClass_surjective_kernel
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) :
    Function.Surjective (affineResidueCycleClass W U p K) ∧
      ∀ x : affineResidueCycles W U p K,
        affineResidueCycleClass W U p K x = 0 ↔
          ∃ y, affineResidueDifferential W U p K 0 1 y = x.val := by
  refine ⟨QuotientAddGroup.mk'_surjective _, ?_⟩
  intro x
  exact QuotientAddGroup.eq_zero_iff x

variable {W U p}

/-- A chain map evaluated and extended to the residue field.
(blueprint: lem-sc-affine-residue-cycle-homology-map)
-/
abbrev affineResidueComponent
    {K C : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ}
    (φ : K ⟶ C) (j : ℤ) :
    affineResidueTerm W U p K j →ₗ[p.ResidueField] affineResidueTerm W U p C j :=
  (show (K.X j).val.obj (.op (Over.mk (𝟙 U))) →ₗ[Γ(W, U)]
    (C.X j).val.obj (.op (Over.mk (𝟙 U))) from
      ((φ.f j).val.app (.op (Over.mk (𝟙 U)))).hom).baseChange p.ResidueField

/-- Evaluation and scalar extension preserve the chain-map commutation equations.
(blueprint: lem-sc-affine-residue-cycle-homology-map)
-/
theorem affineResidueComponent_comm
    {K C : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ}
    (φ : K ⟶ C) (i j : ℤ) :
    (affineResidueDifferential W U p C i j).comp (affineResidueComponent φ i) =
      (affineResidueComponent φ j).comp (affineResidueDifferential W U p K i j) := by
  let F := SheafOfModules.evaluation
    ((moduleRings W.toRingedSpace).over U) (.op (Over.mk (𝟙 U)))
  have h := congrArg (fun g ↦ (F.map g).hom) (φ.comm i j)
  simp only [Functor.map_comp, ModuleCat.hom_comp] at h
  exact (LinearMap.baseChange_comp _ _).symm.trans
    ((congrArg (LinearMap.baseChange p.ResidueField) h).trans
      (LinearMap.baseChange_comp _ _))

/-- The degree-one cycle map of a chain map.
(blueprint: lem-sc-affine-residue-cycle-homology-map)
-/
def affineResidueCycleMap
    {K C : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ}
    (φ : K ⟶ C) : affineResidueCycles W U p K →+ affineResidueCycles W U p C where
  toFun x := ⟨affineResidueComponent φ 1 x.val, by
    change affineResidueDifferential W U p C 1 2 (affineResidueComponent φ 1 x.val) = 0
    rw [← LinearMap.comp_apply, affineResidueComponent_comm, LinearMap.comp_apply]
    rw [x.property, map_zero]⟩
  map_zero' := by ext; exact map_zero _
  map_add' x y := by ext; exact map_add _ _ _

/-- The homology map induced by a chain map on the explicit residue quotient.
(blueprint: lem-sc-affine-residue-cycle-homology-map)
-/
def affineResidueCycleHomologyMap
    {K C : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ}
    (φ : K ⟶ C) : affineResidueCycleHomology W U p K →+
      affineResidueCycleHomology W U p C :=
  QuotientAddGroup.lift (affineResidueBoundaries W U p K)
    ((affineResidueCycleClass W U p C).comp (affineResidueCycleMap φ)) (by
      intro x hx
      apply (affineResidueCycleClass_surjective_kernel W U p C).2 _ |>.mpr
      obtain ⟨y, hy⟩ := hx
      refine ⟨affineResidueComponent φ 0 y, ?_⟩
      change affineResidueDifferential W U p C 0 1 (affineResidueComponent φ 0 y) =
        affineResidueComponent φ 1 x.val
      rw [← LinearMap.comp_apply, affineResidueComponent_comm, LinearMap.comp_apply, hy]
      rfl)

/-- Chain maps commute with the cycle-class projections, including nonzero boundaries.
Source: Stacks Project, Section 12.13, Tag 010V; Mathlib `QuotientAddGroup.lift_mk`.
(blueprint: lem-sc-affine-residue-cycle-homology-map)

Proof: Evaluation and residue scalar extension preserve the chain-map squares.
The square in degrees 1,2 sends cycles to cycles. The square in degrees 0,1
sends the differential of y to the differential of the image of y. Thus the
cycle map descends to the quotient by incoming boundaries. The construction
is QuotientAddGroup.lift, whose value on a cycle class is the class of its
image, by definition. The property of being a cycle is a proposition, so the
result does not depend on which proof of cycle membership is supplied. -/
theorem affineResidueCycleHomologyMap_class
    {K C : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ}
    (φ : K ⟶ C) (x : affineResidueCycles W U p K) :
    affineResidueCycleHomologyMap φ (affineResidueCycleClass W U p K x) =
      affineResidueCycleClass W U p C (affineResidueCycleMap φ x) := rfl

end

end AlgebraicGeometry.Scheme
