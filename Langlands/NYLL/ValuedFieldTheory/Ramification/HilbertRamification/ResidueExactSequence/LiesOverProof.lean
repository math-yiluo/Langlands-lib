/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 173, 2026-11-14: proof of NYLL M243.019
`selectedMaximalIdeal.instLiesOver` (lines 228–234 of
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709). The namespace is
prefixed with Langlands.NYLL; the source instance becomes a theorem whose type is
the published closed target `selectedMaximalIdeal.instLiesOverStatement`,
registered as a global instance by `attribute [instance]`. The source proof
`constructor; rfl` is kept after an `intro` of the closed telescope. The paired
Markdown records all modifications.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Statements

/-!
# The maximal ideal of `A` lies over the contracted ideal

NYLL M243.019: the maximal ideal of the valuation subring `A` lies over its contraction
to the fixed subring `A^{G_w}` of the decomposition group. The theorem is registered
as a global instance.
-/

namespace Langlands.NYLL.RamificationTheory

universe u v

namespace HilbertRamification
namespace ValuationSubring

/-- Provides the instance `instLiesOver`. -/
theorem selectedMaximalIdeal.instLiesOver :
    selectedMaximalIdeal.instLiesOverStatement.{u, v} := by
  intro K L _ _ _ A
  constructor
  rfl

attribute [instance] selectedMaximalIdeal.instLiesOver

/-- Instance search check: the registered instance applies. -/
example (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L) :
    (IsLocalRing.maximalIdeal A).LiesOver (decompositionFixedMaximalIdeal K A) :=
  inferInstance

end ValuationSubring
end HilbertRamification

end Langlands.NYLL.RamificationTheory
