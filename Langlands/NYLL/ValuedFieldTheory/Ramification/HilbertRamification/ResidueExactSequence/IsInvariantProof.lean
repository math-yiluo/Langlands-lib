/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 173, 2026-11-14: proof of NYLL M243.014
`decompositionFixedSubring.instIsInvariant` (lines 172–177 of
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709). The namespace is
prefixed with Langlands.NYLL; the source instance becomes a theorem whose type is
the published closed target `decompositionFixedSubring.instIsInvariantStatement`,
registered as a global instance by `attribute [instance]`. The proof of the private
source helper M243.012 `decompositionFixedSubring_isInvariant` (lines 156–163) is
inlined unchanged after an `intro` of the closed telescope. The paired Markdown
records all modifications.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Statements

/-!
# The fixed subring is the invariant ring of the decomposition group

NYLL M243.014: every element of `A` fixed by the decomposition group `G_w` lies in
the image of the fixed subring `A^{G_w}`, that is,
`Algebra.IsInvariant A^{G_w} A G_w`. The theorem is registered as a global instance.
-/

namespace Langlands.NYLL.RamificationTheory

universe u v

namespace HilbertRamification
namespace ValuationSubring

/-- Provides the instance `instIsInvariant`. -/
theorem decompositionFixedSubring.instIsInvariant :
    decompositionFixedSubring.instIsInvariantStatement.{u, v} := by
  intro K L _ _ _ A
  constructor
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩

attribute [instance] decompositionFixedSubring.instIsInvariant

/-- Instance search check: the registered instance applies. -/
example (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L) :
    Algebra.IsInvariant (decompositionFixedSubring K A) A (decompositionGroup K A) :=
  inferInstance

end ValuationSubring
end HilbertRamification

end Langlands.NYLL.RamificationTheory
