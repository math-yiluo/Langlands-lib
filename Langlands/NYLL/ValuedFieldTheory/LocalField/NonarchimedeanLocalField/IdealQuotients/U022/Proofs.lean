/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 212 on 2026-11-13: extracted M133.022 from
IdealQuotients.lean at fbd320cd8b1b06487c58227e92eb135794267709; added Langlands.NYLL
and the exact named statement target. Local prerequisite adaptations and
private helpers are documented in the paired Markdown.
LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.Statements

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

private theorem chosenIrreducible
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Irreducible (chosenIntegerRingUniformizer K) :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible 𝒪[K])

/-- Proof of the exact source-adapted M133.022 target. -/
theorem maximalIdeal_pow_eq_span_uniformizer_pow
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) :
    maximalIdeal_pow_eq_span_uniformizer_powStatement K n := by
  change (𝓂[K] ^ n : Ideal 𝒪[K]) =
    Ideal.span ({chosenIntegerRingUniformizer K ^ n} : Set 𝒪[K])
  rw [(chosenIrreducible K).maximalIdeal_eq, Ideal.span_singleton_pow]

end Langlands.NYLL.LocalFieldTheory
