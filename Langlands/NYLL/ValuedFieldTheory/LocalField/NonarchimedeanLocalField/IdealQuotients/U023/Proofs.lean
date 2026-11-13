/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 212 on 2026-11-13: extracted M133.023 from
IdealQuotients.lean at fbd320cd8b1b06487c58227e92eb135794267709; added Langlands.NYLL
and the exact named statement target. Local prerequisite adaptations and
private helpers are documented in the paired Markdown.
LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.Statements

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel


/-- Proof of the exact source-adapted M133.023 target. -/
theorem mul_uniformizer_pow_mem_maximalIdeal_pow
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (r : 𝒪[K]) :
    mul_uniformizer_pow_mem_maximalIdeal_powStatement K ϖ hϖ n r := by
  change r * ϖ ^ n ∈ (𝓂[K] ^ n : Ideal 𝒪[K])
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  rw [Ideal.mem_span_singleton]
  exact ⟨r, by rw [mul_comm]⟩

end Langlands.NYLL.LocalFieldTheory
