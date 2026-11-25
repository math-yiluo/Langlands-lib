/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedAction.InternalBar.CondensedInternalBarData
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedFreeLinearization.CondensedFreeLinearizationTensor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-! # Universal contraction of the pointed free deletion complex

Source: blueprint main-20261015, direct-image stability proof, paragraph (3),
extracted internal bar input (blueprint: lem-sfb-pointed-free-deletion-contraction).

Powers, deletion, and insertion are constructed in condensed sets. Their free maps
use the recorded free adjunction. The existence statement specifies the augmentation
and its section on generalized generators; it is never used to choose any definition.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Preadditive
open Profinite.CondensedAction

namespace Profinite.CondensedAction.PointedDeletion

/-- The condensed sets in the prescribed size convention.
Source: blueprint paragraph (3) (blueprint: lem-sfb-pointed-free-deletion-contraction). -/
abbrev Sets := Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))

/-- The actual finite power, including the terminal zero-fold power.
Source: blueprint paragraph (3) (blueprint: lem-sfb-pointed-free-deletion-contraction). -/
def power (X : Sets.{u}) (n : ℕ) : Sets.{u} := ∏ᶜ fun _ : Fin n ↦ X

/-- Delete coordinate i, retaining the order of every other coordinate.
Source: blueprint paragraph (3) (blueprint: lem-sfb-pointed-free-deletion-contraction). -/
def deletion (X : Sets.{u}) (n : ℕ) (i : Fin (n + 1)) :
    power X (n + 1) ⟶ power X n :=
  Pi.lift fun j ↦ Pi.π (fun _ : Fin (n + 1) ↦ X) (i.succAbove j)

/-- The singleton tuple given by a global point.
Source: blueprint paragraph (3) (blueprint: lem-sfb-pointed-free-deletion-contraction). -/
def pointTuple (X : Sets.{u}) (e : ⊤_ Sets.{u} ⟶ X) : ⊤_ Sets.{u} ⟶ power X 1 :=
  Pi.lift fun _ ↦ e

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

/-- Q_n is the canonical free internal module on X^(n+1).
Source: blueprint paragraph (3) (blueprint: lem-sfb-pointed-free-deletion-contraction). -/
def term (X : Sets.{u}) (n : ℕ) : Modules R :=
  (InternalBar.free R).obj (power X (n + 1))

section Proof

set_option backward.isDefEq.respectTransparency false

private abbrev augmentation
    (c : Profinite.CondensedFreeLinearization.Comparison R) (X : Sets.{u}) :
    term R X 0 ⟶ Mod.regular R.X :=
  (InternalBar.free R).map (CartesianMonoidalCategory.toUnit (power X 1)) ≫ c.unit.hom

private abbrev sectionMap
    (c : Profinite.CondensedFreeLinearization.Comparison R)
    (X : Sets.{u}) (e : ⊤_ Sets.{u} ⟶ X) : Mod.regular R.X ⟶ term R X 0 :=
  c.unit.inv ≫ (InternalBar.free R).map
    (terminal.from (𝟙_ Sets.{u}) ≫ pointTuple X e)

end Proof

end Profinite.CondensedAction.PointedDeletion
