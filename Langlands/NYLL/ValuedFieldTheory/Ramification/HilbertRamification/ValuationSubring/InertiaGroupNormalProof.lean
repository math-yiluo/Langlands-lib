/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 122, 2026-11-14: isolate the proof of the instance
M239.005 `inertiaGroup_normal` (lines 58–62 of
Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationSubring.lean)
from commit fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace
with Langlands.NYLL; state it as a theorem of the published closed target
`inertiaGroup_normalStatement` and register it with
`attribute [instance] inertiaGroup_normal`. The source rewrite with the
theorem `residueAction_ker` (M239.004, proved by `rfl`) is replaced by the
definitional `change` to the same kernel, so this module does not import or
repeat that theorem; `infer_instance` is kept. The six Mathlib imports are
replaced by the published statement module.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Statements

/-! # The inertia group is normal in the decomposition group (NYLL M239.005) -/

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring

universe u v

/-- Provides the instance `inertiaGroup_normal`. -/
theorem inertiaGroup_normal : inertiaGroup_normalStatement.{u, v} := by
  intro K L _ _ _ A
  change (MonoidHom.ker (residueAction K A)).Normal
  infer_instance

attribute [instance] inertiaGroup_normal

end Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring
