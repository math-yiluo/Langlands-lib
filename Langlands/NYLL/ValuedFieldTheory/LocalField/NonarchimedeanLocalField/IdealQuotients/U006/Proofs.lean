/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 212 on 2026-11-13: extracted M133.006 from
IdealQuotients.lean at fbd320cd8b1b06487c58227e92eb135794267709;
added Langlands.NYLL and the exact statement target. Its earlier M133.005
input is proved locally under a private non-conflicting name by the original
choice-specification term. LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.Statements

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

private theorem chosenUniformizerIrreducible
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Irreducible (chosenIntegerRingUniformizer K) :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible 𝒪[K])

/-- The chosen uniformizer generates the maximal ideal. -/
theorem chosenIntegerRingUniformizer_maximalIdeal_eq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    chosenIntegerRingUniformizer_maximalIdeal_eqStatement K :=
  (chosenUniformizerIrreducible K).maximalIdeal_eq

end Langlands.NYLL.LocalFieldTheory
