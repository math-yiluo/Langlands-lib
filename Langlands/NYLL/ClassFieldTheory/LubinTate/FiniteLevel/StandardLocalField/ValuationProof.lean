/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 319, 2026-11-16: extract only the proof of M335.003
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; prefix
the namespace with Langlands.NYLL, import the published comparison
statements, and state the theorem with the fully applied imported target.
Unfold that target before the original proof. Replace the module
documentation and omit opens unused by this unit. The original license
and notices are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.Statements

/-!
# The valuation of the canonical local-field package

The canonical local-field package carries the valuation attached to the
given valuative relation.
-/

noncomputable section

open scoped ValuativeRel

namespace Langlands.NYLL.LubinTate

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The valuation in the canonical local-field package is the valuation
attached to the given valuative relation. -/
theorem standardLocalField_valuation_eq :
    standardLocalField_valuation_eqStatement K := by
  unfold standardLocalField_valuation_eqStatement
  unfold standardLocalField
  unfold LocalFieldTheory.localCompleteDVF
  unfold ValuationTheory.Valuations.completeDVFOfCompleteValuedField
  rfl

end Langlands.NYLL.LubinTate
