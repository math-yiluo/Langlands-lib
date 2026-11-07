/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 1686 from ClassFieldTheory commit
fbd320cd8b1b06487c58227e92eb135794267709:
M422.006's complete signature is packaged as a universal Prop target in
Langlands.NYLL. The private smallness wrapper is replaced by local use of
the published smallness theorem, and the published transported valuative
relation is installed locally. The proof is reserved for a separate unit.
The original license and notice are retained in licenses/NYLL/LICENSE and
licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkValuativeRel

/-!
# Strict comparison of canonical valuations on a local field and its Shrink

The target compares strict orders in the two canonical value groups along
`Shrink.ringEquiv K`, with the published smallness proof and transported
valuative relation installed locally.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- Strict comparisons for the canonical valuation on `Shrink.{0} K`, with
the published transported relation, agree with strict comparisons for the
canonical valuation on `K` along `Shrink.ringEquiv K`. This definition
states the universal target; its proof is a separate unit. -/
def shrinkLocalField_valuation_lt_iffStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    letI : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    ∀ x y : Shrink.{0} K,
      ValuativeRel.valuation (Shrink.{0} K) x < ValuativeRel.valuation (Shrink.{0} K) y ↔
        ValuativeRel.valuation K (Shrink.ringEquiv K x) <
          ValuativeRel.valuation K (Shrink.ringEquiv K y)

end Langlands.NYLL.LocalFieldTheory
