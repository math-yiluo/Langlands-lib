/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 773, 2026-11-16: extract M335.002 (lines 48–54)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; prefix
the namespace with Langlands.NYLL, import the published Statements module,
and express the theorem type as its exact applied proposition target.
Unfold that target before the source reflexivity proof; retain the source
simp attribute, docstring and section telescope. Replace the module
documentation and omit unused opens. See the paired Markdown.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.Statements

/-!
# Forgetting the canonical local-field package to a complete DVF

The canonical local-field package has the published canonical complete
discrete valuation as its parent, by definitional equality.
-/

noncomputable section

namespace Langlands.NYLL.LubinTate

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Forgetting residue-field finiteness recovers the canonical complete-DVF
package used by finite local reciprocity. -/
@[simp]
theorem standardLocalField_toCompleteDVF :
    standardLocalField_toCompleteDVFStatement K := by
  unfold standardLocalField_toCompleteDVFStatement
  rfl

end Langlands.NYLL.LubinTate
