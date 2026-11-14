/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 173, 2026-11-14: proof of NYLL M243.007
`decompositionFixedSubring.instIsLocalRing` (lines 96–100 of
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709). The namespace is
prefixed with Langlands.NYLL; the source instance becomes a theorem whose type
is the published closed target
`decompositionFixedSubring.instIsLocalRingStatement`. The source proof (transport
along `decompositionFieldValuationSubringEquivFixedSubring`) is replaced by the
published Library instance `FixedPoints.isLocalRing_subring`, which already
supplies this instance, so no second global instance is registered. The paired
Markdown records all modifications.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Statements
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal

/-!
# The fixed subring of the decomposition group is local

NYLL M243.007: for a valuation subring `A` of `L`, the fixed subring `A^{G_w}` of the
decomposition group `G_w` of `A` over `K` is a local ring. The published global
instance `FixedPoints.isLocalRing_subring` (fixed subrings of a local ring under a
monoid acting by ring automorphisms are local) already supplies this instance, so it is
used here and not registered a second time.
-/

namespace Langlands.NYLL.RamificationTheory

universe u v

namespace HilbertRamification
namespace ValuationSubring

/-- The fixed subring of the decomposition group is a local ring. Instance search
finds this through the existing global instance `FixedPoints.isLocalRing_subring`,
so this theorem is not registered as a second instance. -/
theorem decompositionFixedSubring.instIsLocalRing :
    decompositionFixedSubring.instIsLocalRingStatement.{u, v} := by
  intro K L _ _ _ A
  exact FixedPoints.isLocalRing_subring

/-- Instance search check: the existing instance applies to the fixed subring. -/
example (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L) :
    IsLocalRing (decompositionFixedSubring K A) :=
  inferInstance

end ValuationSubring
end HilbertRamification

end Langlands.NYLL.RamificationTheory
