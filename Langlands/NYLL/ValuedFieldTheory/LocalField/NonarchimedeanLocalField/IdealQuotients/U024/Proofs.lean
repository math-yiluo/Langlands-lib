/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 212 on 2026-11-13: extracted M133.024 from
IdealQuotients.lean at fbd320cd8b1b06487c58227e92eb135794267709; added Langlands.NYLL
and the exact named statement target. Local prerequisite adaptations and
private helpers are documented in the paired Markdown.
LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.Statements

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel


/-- Proof of the exact source-adapted M133.024 target. -/
theorem mul_uniformizer_pow_mem_maximalIdeal_pow_succ_iff
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (r : 𝒪[K]) :
    mul_uniformizer_pow_mem_maximalIdeal_pow_succ_iffStatement K ϖ hϖ n r := by
  change r * ϖ ^ n ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) ↔
    r ∈ (𝓂[K] : Ideal 𝒪[K])
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hne : ϖ ^ n ≠ 0 := pow_ne_zero n hϖ.ne_zero
    have hcancel : r * ϖ ^ n = (ϖ * c) * ϖ ^ n := by
      calc
        r * ϖ ^ n = ϖ ^ (n + 1) * c := hc
        _ = (ϖ * c) * ϖ ^ n := by
          rw [pow_succ']
          ring
    exact mul_right_cancel₀ hne hcancel
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [hc]
    rw [pow_succ']
    ring

end Langlands.NYLL.LocalFieldTheory
