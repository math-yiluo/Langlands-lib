/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 173, 2026-11-14: proof of NYLL M243.013
`decompositionFixedSubring.instSMulCommClass` (lines 165–170 of
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709, with its private
helper M243.011 at lines 146–154). The namespace is prefixed with Langlands.NYLL;
the source instance becomes a theorem whose type is the published closed target
`decompositionFixedSubring.instSMulCommClassStatement`. The source proof through
the private helper is replaced by Mathlib's instance on `FixedPoints.subring`,
which already supplies this instance, so no second global instance is
registered. The paired Markdown records all modifications.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Statements

/-!
# The decomposition group action commutes with the fixed subring

NYLL M243.013: the action of the decomposition group `G_w` on `A` commutes with
multiplication by elements of the fixed subring `A^{G_w}`. Mathlib's instance
`SMulCommClass G (FixedPoints.subring B G) B` already supplies this instance, so it is
used here and not registered a second time.
-/

namespace Langlands.NYLL.RamificationTheory

universe u v

namespace HilbertRamification
namespace ValuationSubring

/-- The decomposition group action on `A` commutes with multiplication by the fixed
subring. Instance search finds this through Mathlib's instance
`instSMulCommClassSubtypeMemSubringSubring`, so this theorem is not registered as a
second instance. -/
theorem decompositionFixedSubring.instSMulCommClass :
    decompositionFixedSubring.instSMulCommClassStatement.{u, v} := by
  intro K L _ _ _ A
  exact instSMulCommClassSubtypeMemSubringSubring A (decompositionGroup K A)

/-- Instance search check: Mathlib's instance applies to the fixed subring. -/
example (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L) :
    SMulCommClass (decompositionGroup K A) (decompositionFixedSubring K A) A :=
  inferInstance

end ValuationSubring
end HilbertRamification

end Langlands.NYLL.RamificationTheory
