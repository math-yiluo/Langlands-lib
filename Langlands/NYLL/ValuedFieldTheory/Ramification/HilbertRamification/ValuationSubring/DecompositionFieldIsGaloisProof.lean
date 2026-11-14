/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 122, 2026-11-14: isolate the proof of the instance
M239.038 `decompositionField_isGalois` (lines 368–374 of
Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationSubring.lean)
from commit fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace
with Langlands.NYLL; state it as a theorem of the published closed target
`decompositionField_isGaloisStatement`, introducing the source section
variables, `[FiniteDimensional K L]` and `A` before the original term
`IsGalois.of_fixed_field L (decompositionGroup K A)`, and register it with
`attribute [instance] decompositionField_isGalois`. The six Mathlib imports
are replaced by the published statement module.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Statements

/-! # `L` is Galois over the decomposition field (NYLL M239.038) -/

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring

universe u v

/-- The fixed-field description of decomposition source:
`L/Z_w` is Galois because `Z_w` is the fixed field of the finite
decomposition group action. -/
theorem decompositionField_isGalois : decompositionField_isGaloisStatement.{u, v} := by
  intro K L _ _ _ _ A
  exact IsGalois.of_fixed_field L (decompositionGroup K A)

attribute [instance] decompositionField_isGalois

end Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring
