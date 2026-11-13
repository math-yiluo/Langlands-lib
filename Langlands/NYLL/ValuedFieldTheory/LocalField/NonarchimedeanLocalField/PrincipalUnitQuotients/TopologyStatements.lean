/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Adapted by Worker 211 from pinned NYLL PrincipalUnitQuotients.lean.
-- See the paired Markdown for source lines, exact modifications and attribution.

import Mathlib.NumberTheory.LocalField.Basic

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

open Filter

/-- Exact source target M132.012. -/
def exists_maximalIdeal_pow_subset_nhds_zeroStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (s : Set 𝒪[K])
    (hs : s ∈ nhds (0 : 𝒪[K])) : Prop :=
  ∃ N : Nat, ((𝓂[K] ^ N : Ideal 𝒪[K]) : Set 𝒪[K]) ⊆ s

/-- Exact source target M132.013. -/
def eventually_maximalIdeal_pow_subset_nhds_zeroStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (s : Set 𝒪[K])
    (hs : s ∈ nhds (0 : 𝒪[K])) : Prop :=
  ∃ N : Nat, ∀ m : Nat, N ≤ m →
      ((𝓂[K] ^ m : Ideal 𝒪[K]) : Set 𝒪[K]) ⊆ s

/-- Exact source target M132.014. -/
def isClosed_maximalIdeal_powStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) : Prop :=
  IsClosed (((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]))

/-- Exact source target M132.015. -/
def maximalIdeal_pow_mem_nhds_zeroStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) : Prop :=
  (((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])) ∈ nhds (0 : 𝒪[K])

/-- Exact source target M132.016. -/
def tendsto_pow_succ_of_mem_maximalIdealStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {x : 𝒪[K]}
    (hx : x ∈ (𝓂[K] : Ideal 𝒪[K])) : Prop :=
  Tendsto (fun d : Nat => x ^ (d + 1)) atTop (nhds (0 : 𝒪[K]))

/-- Exact source target M132.017. -/
def tendsto_neg_pow_succ_of_mem_maximalIdealStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {x : 𝒪[K]}
    (hx : x ∈ (𝓂[K] : Ideal 𝒪[K])) : Prop :=
  Tendsto (fun d : Nat => (-x) ^ (d + 1)) atTop (nhds (0 : 𝒪[K]))


end

end Langlands.NYLL.LocalFieldTheory
