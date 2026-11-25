/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.Coherent.CoherentSheaves
public import WeilConjectures.CategoryTheory.CondensedActionModule
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.CategoryTheory.SheafTensorStructure

/-! # The augmented internal homogeneous bar resolution

Source: blueprint, direct-image stability, paragraph (3), formal internal bar input
(auxiliary; not a blueprint node).

Free objects are the actual composite of free abelian sheaf and free internal module.
The resolution specification retains all generator formulas, including the equivariant
induced presentation. No object is selected from the postponed existence theorem.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Profinite.CondensedAction
open scoped TensorProduct

namespace Profinite.CondensedAction.InternalBar

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

/-- The free internal module on a condensed set, by the two free adjunctions.
Source: the free-module construction in step 1 of the internal bar proof
(auxiliary; not a blueprint node). -/
def free : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)) ⥤ Modules R :=
  Sheaf.composeAndSheafify (coherentTopology Profinite.{u}) AddCommGrpCat.free.{u + 1} ⋙
    Mod.free R.X

variable (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

end Profinite.CondensedAction.InternalBar
