/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 122, 2026-11-14: isolate the proof of M239.004
`residueAction_ker` (lines 53–56 of
Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationSubring.lean)
from commit fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace
with Langlands.NYLL; state the theorem as the published closed target
`residueAction_kerStatement`, so the source section variables and the
binder `A` are introduced in the proof before the original `rfl`; replace
the six Mathlib imports by the published statement module.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Statements

/-! # The inertia group is the kernel of the residue action (NYLL M239.004) -/

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring

universe u v

/-- The inertia group is the kernel of the residue action. -/
theorem residueAction_ker : residueAction_kerStatement.{u, v} := by
  intro K L _ _ _ A
  rfl

end Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring
