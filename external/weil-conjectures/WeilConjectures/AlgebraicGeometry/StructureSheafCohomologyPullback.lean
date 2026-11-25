/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Functors

/-!
# Pullback on structure sheaf cohomology

Source: Stacks Project, Varieties, Tag 0BED, the functoriality maps in the proof
(blueprint: def-sc-structure-sheaf-cohomology-pullback).

## Main definitions

- `AlgebraicGeometry.Scheme.structureSheafAb`: the structure sheaf with its additive groups.
- `AlgebraicGeometry.Scheme.structureSheafCohomologyPullback`: canonical pullback on cohomology.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- The underlying abelian sheaf of the structure sheaf. Source: Stacks Project,
Varieties, Tag 0BED (blueprint: def-sc-structure-sheaf-cohomology-pullback). -/
noncomputable def structureSheafAb (X : Scheme.{v}) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v} :=
  (sheafCompose _
    (forget₂ CommRingCat RingCat.{v} ⋙ forget₂ RingCat AddCommGrpCat.{v})).obj X.sheaf

/-- Pullback on structure sheaf cohomology: apply the exact inverse-image functor to
an Ext class, compare the constant integer sheaves, and then apply the adjoint of the
structure morphism on sheaves. Source: Stacks Project, Varieties, Tag 0BED, proof;
Cohomology of Sheaves, Section 01F7
(blueprint: def-sc-structure-sheaf-cohomology-pullback). -/
noncomputable def structureSheafCohomologyPullback {X Y : Scheme.{v}} (f : X ⟶ Y) (n : ℕ) :
    Sheaf.H (structureSheafAb Y) n →+ Sheaf.H (structureSheafAb X) n :=
  letI := lan_preservesFiniteLimits_of_flat (E := AddCommGrpCat.{v}) (Opens.map f.base)
  letI : PreservesFiniteLimits ((Opens.map f.base).sheafPullback AddCommGrpCat.{v}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _
  letI := ((Opens.map f.base).sheafAdjunctionContinuous AddCommGrpCat.{v}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).leftAdjoint_preservesColimits
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts
    ((Opens.map f.base).sheafPullback AddCommGrpCat.{v}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X))
  letI := Functor.additive_of_preservesBinaryBiproducts
    ((Opens.map f.base).sheafPullback AddCommGrpCat.{v}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X))
  (Sheaf.H.map
    (((Opens.map f.base).sheafAdjunctionContinuous AddCommGrpCat.{v} _ _).homEquiv _ _ |>.symm
      (⟨Functor.whiskerRight f.c
        (forget₂ CommRingCat RingCat.{v} ⋙ forget₂ RingCat AddCommGrpCat.{v})⟩)) n).comp
    (Sheaf.H.mapFunctor ((Opens.map f.base).sheafPullback AddCommGrpCat.{v}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X))
      (((Opens.map f.base).constantSheafsheafPullbackIso AddCommGrpCat.{v} _ _
        isTerminalTop isTerminalTop).symm.app (AddCommGrpCat.of (ULift ℤ)))
      (structureSheafAb Y) n)

end AlgebraicGeometry.Scheme
