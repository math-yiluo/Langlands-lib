/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 3, 2026-11-13: state only M249.007, lines 94–98 of
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709, as the closed
proposition localSeparableValuationSubring_pullbackStatement in the
Langlands.NYLL.LocalClassFieldTheory namespace; the section variables of the
source become its leading universally quantified binders; the source proof is
not part of this module. The retained license and notices are in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U006.Definitions

/-!
# Pullback of the chosen separable valuation ring: target

This module states only M249.007, lines 94–98 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- Closed target for NYLL M249.007: pulling the chosen valuation ring of
`SeparableClosure K` back along `K → SeparableClosure K` recovers the valuation
ring of the canonical complete discrete valuation of `K`. -/
def localSeparableValuationSubring_pullbackStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : K),
    algebraMap K (SeparableClosure K) x ∈
        localSeparableValuationSubring K ↔
      x ∈ (Langlands.NYLL.LocalFieldTheory.localCompleteDVF K).valuation.valuationSubring

end Langlands.NYLL.LocalClassFieldTheory
