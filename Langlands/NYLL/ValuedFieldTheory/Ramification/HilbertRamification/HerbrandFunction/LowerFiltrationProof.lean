/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 60, 2026-11-01, with source extraction and proof routing
contributed by Worker 106:
extract M305.002 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix namespaces with
Langlands.NYLL, and prove the published closed target by introducing its
binders before the original rfl proof. Retain the source theorem name
and simp attribute, all four independent universes and all natural indices.
Import the actual construction through its unchanged published statement.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.LowerFiltrationStatement

/-!
# Natural-level projection of the actual lower filtration: proof

M305.002 of the pinned NYLL `HerbrandFunction.lean`, proved as the exact
published closed proposition without additional mathematical parameters.
-/

universe u v w x

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

/-- The actual lower filtration projects to its defining real lower group
at every natural index, under exactly the supplied unique-extension data. -/
@[simp] theorem lowerRamificationFiltrationOfUniqueExtension_lower :
    LowerRamificationFiltrationProjectionStatement.{u, v, w, x} := by
  intro K L instK instL instAlg base target instExt huniq n
  rfl

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
