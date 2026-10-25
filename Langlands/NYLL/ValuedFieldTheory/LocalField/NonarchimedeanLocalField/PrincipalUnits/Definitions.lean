/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Adapted from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709,
-- PrincipalUnits.lean, lines 19–50. See Definitions.md and licenses/NYLL/.

import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.Ring

/-!
# Principal-unit subgroups of valuation-ring units

The subgroup consists of integer-ring units congruent to one modulo a power
of the canonical maximal ideal. The index ranges over all natural numbers.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The actual principal-unit filtration `U^n = {u ∈ 𝒪[K]ˣ | u - 1 ∈ 𝓂[K]^n}`. -/
def principalUnits (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    Subgroup 𝒪[K]ˣ where
  carrier := {u | ((u : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K])}
  one_mem' := by
    change (1 : 𝒪[K]) - 1 ∈ (𝓂[K] ^ n : Ideal 𝒪[K])
    rw [sub_self]
    exact (𝓂[K] ^ n : Ideal 𝒪[K]).zero_mem
  mul_mem' := by
    intro a b ha hb
    change ((a : 𝒪[K]) * (b : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K])
    rw [show ((a : 𝒪[K]) * (b : 𝒪[K]) - 1) =
        ((a : 𝒪[K]) - 1) * (b : 𝒪[K]) + ((b : 𝒪[K]) - 1) by
      ring]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) hb
  inv_mem' := by
    intro a ha
    change (((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K])
    rw [show (((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) - 1) =
        -(((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * ((a : 𝒪[K]) - 1)) by
      calc
        (((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) - 1)
            = ((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K])
              - (((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * (a : 𝒪[K])) := by
                rw [Units.inv_mul]
        _ = -(((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * ((a : 𝒪[K]) - 1)) := by
          ring]
    exact (𝓂[K] ^ n : Ideal 𝒪[K]).neg_mem (Ideal.mul_mem_left _ _ ha)

end

end Langlands.NYLL.LocalFieldTheory
