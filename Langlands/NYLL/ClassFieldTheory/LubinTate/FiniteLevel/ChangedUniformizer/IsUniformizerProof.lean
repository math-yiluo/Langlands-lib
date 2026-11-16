/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 231, 2026-11-16: extract the proof of M391.003
(lines 69–76) at upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
qualify the namespace with Langlands.NYLL, replace the upstream imports
by the published exact statement module, and introduce its closed
proposition's binders before the unchanged mathematical proof.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer.Statements

/-!
# Preservation of a uniformizer under a unit change

The exact proof of the published target for source unit M391.003.
-/

universe u v

namespace Langlands.NYLL.LubinTate

/-- Multiplication by a valuation-ring unit preserves the uniformizer property. -/
theorem standardLubinTateChangedUniformizer_isUniformizer :
    standardLubinTateChangedUniformizer_isUniformizerStatement.{u, v} := by
  intro K _ F π hπ a
  exact hπ.of_associated
    (associated_unit_mul_right π (a : F.valuationSubring) a.isUnit)

end Langlands.NYLL.LubinTate
