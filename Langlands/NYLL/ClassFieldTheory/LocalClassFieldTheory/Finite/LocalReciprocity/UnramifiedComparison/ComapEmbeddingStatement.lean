/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 3, 2026-11-13: state only M265.012, lines 163–166 of
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedComparison.lean
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709, as the closed
proposition localSeparableValuationSubring_comap_embeddingStatement in the
Langlands.NYLL.LocalClassFieldTheory namespace; the section variables of the
source that the theorem uses become its leading universally quantified
binders; the source proof is not part of this module. The retained license
and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U006.Definitions

/-!
# Pulling the chosen separable valuation ring back along an embedding: target

This module states only M265.012, lines 163–166 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedComparison.lean`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- Closed target for NYLL M265.012: for a finite separable extension `L/K`
of a nonarchimedean local field `K`, with a valuation on `L` extending that of
`K`, pulling the chosen valuation ring of `SeparableClosure K` back along a
`K`-embedding `L → SeparableClosure K` gives the valuation ring of `L`. -/
def localSeparableValuationSubring_comap_embeddingStatement : Prop :=
  ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [Algebra K L]
    [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (i : L →ₐ[K] SeparableClosure K) [Algebra.IsSeparable K L],
    (localSeparableValuationSubring K).comap i.toRingHom =
      (ValuativeRel.valuation L).valuationSubring

end Langlands.NYLL.LocalClassFieldTheory
