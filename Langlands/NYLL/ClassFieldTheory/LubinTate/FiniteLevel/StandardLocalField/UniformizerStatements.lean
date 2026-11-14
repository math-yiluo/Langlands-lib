/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 412, 2026-11-14: extract only the assertion of M335.021
(lines 300–304) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued target; rename the
theorem `standardLocalFieldUniformizer_isUniformizer` to the target
`standardLocalFieldUniformizer_isUniformizerStatement`, omit its proof
(lines 304–312), prefix the namespace with Langlands.NYLL, replace the six
source imports by the M335.019 module, and replace the module
documentation. See the paired Markdown for the complete record.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.Uniformizer

/-!
# Target: the transported canonical uniformizer is a uniformizer

The Prop-valued target of the source theorem
`LubinTate.standardLocalFieldUniformizer_isUniformizer` in
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean`.
No proof is supplied here.
-/

namespace Langlands.NYLL.LubinTate

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Target of the source theorem `standardLocalFieldUniformizer_isUniformizer`:
the transported canonical prime element is a uniformizer for the valuation in
the standard local-field package, in the sense of Mathlib's
`Valuation.IsUniformizer`. -/
def standardLocalFieldUniformizer_isUniformizerStatement : Prop :=
  (standardLocalField K).valuation.IsUniformizer
    (standardLocalFieldUniformizer K : K)

end Langlands.NYLL.LubinTate
