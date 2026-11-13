/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Adapted from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709,
-- QuotientReps.lean, lines 27–56 and 87–93. See Definitions.md and licenses/NYLL/.

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Definitions
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Integer units modulo principal units at a level

The named quotient, its commutative group, concrete equivalence, canonical
projection and homomorphism lift retain the source constructions.
-/

namespace Langlands.NYLL.CyclicCohomology

open Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Integer units modulo the `n`-th principal-unit subgroup.

This named type is the representation boundary: downstream code uses its
quotient interface rather than unfolding the concrete quotient. -/
def IntegerUnitsModPrincipalUnitsAtLevel
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) : Type u :=
  𝒪[K]ˣ ⧸ principalUnits K n

/-- Integer units modulo level principal units form a commutative group. -/
instance integerUnitsModPrincipalUnitsAtLevelCommGroup
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    CommGroup (IntegerUnitsModPrincipalUnitsAtLevel K n) := by
  change CommGroup (𝒪[K]ˣ ⧸ principalUnits K n)
  infer_instance

/-- Explicit comparison with the concrete quotient implementation. -/
def integerUnitsModPrincipalUnitsAtLevelConcreteEquiv
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    IntegerUnitsModPrincipalUnitsAtLevel K n ≃*
      (𝒪[K]ˣ ⧸ principalUnits K n) := by
  change (𝒪[K]ˣ ⧸ principalUnits K n) ≃*
    (𝒪[K]ˣ ⧸ principalUnits K n)
  exact MulEquiv.refl _

/-- The canonical class of an integer unit modulo `U_K^n`. -/
def integerUnitsModPrincipalUnitsAtLevelMk
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    𝒪[K]ˣ →* IntegerUnitsModPrincipalUnitsAtLevel K n := by
  change 𝒪[K]ˣ →* (𝒪[K]ˣ ⧸ principalUnits K n)
  exact QuotientGroup.mk' (principalUnits K n)

/-- Descend a homomorphism that kills `U_K^n`. -/
def integerUnitsModPrincipalUnitsAtLevelLift
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]
    (n : Nat) (f : 𝒪[K]ˣ →* M) (h : principalUnits K n ≤ f.ker) :
    IntegerUnitsModPrincipalUnitsAtLevel K n →* M := by
  change (𝒪[K]ˣ ⧸ principalUnits K n) →* M
  exact QuotientGroup.lift (principalUnits K n) f h

end

end Langlands.NYLL.CyclicCohomology
