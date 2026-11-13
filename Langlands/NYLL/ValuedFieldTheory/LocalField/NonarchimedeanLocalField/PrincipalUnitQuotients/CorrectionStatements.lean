/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Adapted by Worker 211 from pinned NYLL PrincipalUnitQuotients.lean.
-- See the paired Markdown for source lines, exact modifications and attribution.

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.CorrectionDefinitions
import Mathlib.NumberTheory.LocalField.Basic

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

open Filter

/-- Exact source target M132.022. -/
def principalUnitsCorrectionProduct_succStatement
    (K : Type u) [Field K] [ValuativeRel K] (n d : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) : Prop :=
  principalUnitsCorrectionProduct K n z (d + 1) =
      principalUnitsCorrectionProduct K n z d * (z d : 𝒪[K]ˣ)

/-- Exact source target M132.023. -/
def principalUnitsCorrectionProduct_memStatement
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) (d : Nat) : Prop :=
  principalUnitsCorrectionProduct K n z d ∈ principalUnits K n

/-- Exact source target M132.024. -/
def principalUnitsCorrectionProduct_div_memStatement
    (K : Type u) [Field K] [ValuativeRel K] (n m d : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) : Prop :=
  principalUnitsCorrectionProduct K n z (m + d) /
        principalUnitsCorrectionProduct K n z m ∈
      principalUnits K (n + m)

/-- Exact source target M132.025. -/
def principalUnitsCorrectionProduct_div_sub_one_memStatement
    (K : Type u) [Field K] [ValuativeRel K] (n m d : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) : Prop :=
  ((principalUnitsCorrectionProduct K n z (m + d) /
          principalUnitsCorrectionProduct K n z m : 𝒪[K]ˣ) : 𝒪[K]) - 1 ∈
      (𝓂[K] ^ (n + m) : Ideal 𝒪[K])

/-- Exact source target M132.026. -/
def unit_sub_eq_mul_div_sub_oneStatement
    (K : Type u) [Field K] [ValuativeRel K] (a b : 𝒪[K]ˣ) : Prop :=
  (a : 𝒪[K]) - (b : 𝒪[K]) =
      (b : 𝒪[K]) * (((a / b : 𝒪[K]ˣ) : 𝒪[K]) - 1)

/-- Exact source target M132.027. -/
def principalUnitsCorrectionProduct_sub_memStatement
    (K : Type u) [Field K] [ValuativeRel K] (n m d : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) : Prop :=
  ((principalUnitsCorrectionProduct K n z (m + d) : 𝒪[K]ˣ) : 𝒪[K]) -
        ((principalUnitsCorrectionProduct K n z m : 𝒪[K]ˣ) : 𝒪[K]) ∈
      (𝓂[K] ^ (n + m) : Ideal 𝒪[K])

/-- Exact source target M132.028. -/
def principalUnitsCorrectionProduct_sub_mem_of_leStatement
    (K : Type u) [Field K] [ValuativeRel K] (n N i j : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d))
    (hi : N ≤ i) (hj : N ≤ j) : Prop :=
  ((principalUnitsCorrectionProduct K n z i : 𝒪[K]ˣ) : 𝒪[K]) -
        ((principalUnitsCorrectionProduct K n z j : 𝒪[K]ˣ) : 𝒪[K]) ∈
      (𝓂[K] ^ (n + N) : Ideal 𝒪[K])

/-- Exact source target M132.029. -/
def principalUnitsCorrectionProduct_cauchySeqStatement
    (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsNonarchimedeanLocalField K] (n : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) : Prop :=
  CauchySeq fun d : Nat =>
      ((principalUnitsCorrectionProduct K n z d : 𝒪[K]ˣ) : 𝒪[K])

/-- Exact source target M132.030. -/
def exists_tendsto_principalUnitsCorrectionProductStatement
    (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsNonarchimedeanLocalField K] (n : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) : Prop :=
  ∃ x : 𝒪[K], Tendsto
      (fun d : Nat => ((principalUnitsCorrectionProduct K n z d : 𝒪[K]ˣ) : 𝒪[K]))
      atTop (nhds x)

/-- Exact source target M132.031. -/
def principalUnitsCorrectionProduct_limit_sub_one_memStatement
    (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsNonarchimedeanLocalField K] (n : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) (x : 𝒪[K])
    (hx : Tendsto
      (fun d : Nat => ((principalUnitsCorrectionProduct K n z d : 𝒪[K]ˣ) : 𝒪[K]))
      atTop (nhds x)) : Prop :=
  x - 1 ∈ (𝓂[K] ^ n : Ideal 𝒪[K])

/-- Exact source target M132.032. -/
def exists_tendsto_principalUnitsCorrectionProduct_sub_one_memStatement
    (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsNonarchimedeanLocalField K] (n : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) : Prop :=
  ∃ x : 𝒪[K], Tendsto
        (fun d : Nat => ((principalUnitsCorrectionProduct K n z d : 𝒪[K]ˣ) : 𝒪[K]))
        atTop (nhds x) ∧
      x - 1 ∈ (𝓂[K] ^ n : Ideal 𝒪[K])

/-- Exact source target M132.076. -/
def exists_tendsto_principalUnitsCorrectionProduct_principalUnitStatement
    (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsNonarchimedeanLocalField K] (n : Nat) (hn : 1 ≤ n)
    (z : ∀ d : Nat, principalUnits K (n + d)) : Prop :=
  ∃ x : principalUnits K n, Tendsto
      (fun d : Nat => ((principalUnitsCorrectionProduct K n z d : 𝒪[K]ˣ) : 𝒪[K]))
      atTop (nhds (((x : principalUnits K n) : 𝒪[K]ˣ) : 𝒪[K]))


end

end Langlands.NYLL.LocalFieldTheory
