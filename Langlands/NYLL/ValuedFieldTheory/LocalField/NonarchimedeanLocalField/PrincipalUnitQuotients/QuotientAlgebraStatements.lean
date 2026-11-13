/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Adapted by Worker 211 from pinned NYLL PrincipalUnitQuotients.lean.
-- See the paired Markdown for source lines, exact modifications and attribution.

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.SuccessorDefinitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.MaximalIdealDefinitions

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

open Filter

/-- Exact source target M132.040. -/
def principalUnitsSuccQuotMk_surjectiveStatement
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) : Prop :=
  Function.Surjective (principalUnitsSuccQuotMk K n)

/-- Exact source target M132.046. -/
def principalUnitsSuccQuotMk_eq_one_iffStatement
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (u : principalUnits K n) : Prop :=
  principalUnitsSuccQuotMk K n u = 1 ↔
      u ∈ (principalUnits K (n + 1)).subgroupOf (principalUnits K n)

/-- Exact source target M132.048. -/
def principalUnitsSuccQuotMk_eq_iff_div_memStatement
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (u v : principalUnits K n) : Prop :=
  principalUnitsSuccQuotMk K n u = principalUnitsSuccQuotMk K n v ↔
      u / v ∈ (principalUnits K (n + 1)).subgroupOf (principalUnits K n)

/-- Exact source target M132.053. -/
def mem_principalUnits_succ_subgroupOf_iffStatement
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (u : principalUnits K n) : Prop :=
  u ∈ (principalUnits K (n + 1)).subgroupOf (principalUnits K n) ↔
      (((u : 𝒪[K]ˣ) : 𝒪[K]) - 1) ∈
        (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])

/-- Exact source target M132.062. -/
protected def MaximalIdealPowSuccQuot.inductionOnStatement
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : MaximalIdealPowSuccQuot K n → Prop}
    (q : MaximalIdealPowSuccQuot K n)
    (h : ∀ a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u),
      motive (maximalIdealPowSuccQuotMk K n a)) : Prop :=
  motive q

/-- Exact source target M132.063. -/
protected def MaximalIdealPowSuccQuot.inductionOn₂Statement
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : MaximalIdealPowSuccQuot K n →
      MaximalIdealPowSuccQuot K n → Prop}
    (q r : MaximalIdealPowSuccQuot K n)
    (h : ∀ a b : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u),
      motive (maximalIdealPowSuccQuotMk K n a)
        (maximalIdealPowSuccQuotMk K n b)) : Prop :=
  motive q r

/-- Exact source target M132.068. -/
def mem_maximalIdealPowSuccSubmodule_iffStatement
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u)) : Prop :=
  a ∈ maximalIdealPowSuccSubmodule K n ↔
      (a : 𝒪[K]) ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])

/-- Exact source target M132.069. -/
def maximalIdealPowSuccQuotMk_eq_zero_iffStatement
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u)) : Prop :=
  maximalIdealPowSuccQuotMk K n a = 0 ↔
      (a : 𝒪[K]) ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])

/-- Exact source target M132.071. -/
def isUnit_one_add_of_mem_maximalIdeal_powStatement
    (K : Type u) [Field K] [ValuativeRel K] {n : Nat} (hn : 1 ≤ n)
    (a : 𝒪[K]) (ha : a ∈ (𝓂[K] ^ n : Ideal 𝒪[K])) : Prop :=
  IsUnit (1 + a)

/-- Exact source target M132.086. -/
def maximalIdealPow_mul_mem_succStatement
    (K : Type u) [Field K] [ValuativeRel K] {n : Nat} (hn : 1 ≤ n)
    (a b : (𝓂[K] ^ n : Ideal 𝒪[K])) : Prop :=
  ((a : 𝒪[K]) * (b : 𝒪[K])) ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])


end

end Langlands.NYLL.LocalFieldTheory
