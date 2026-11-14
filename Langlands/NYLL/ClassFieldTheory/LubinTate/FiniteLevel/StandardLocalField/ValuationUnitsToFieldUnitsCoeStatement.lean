/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 413, 2026-11-14: extract only the statement of M335.016
(lines 236–244) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued target; prefix the
namespace with Langlands.NYLL, append the Statement suffix, turn the theorem
parameter into a definition parameter, omit the proof and the simp attribute,
replace the six source imports by the focused import below, and replace the
module overview. See the paired Markdown for the complete modification record
and licenses/NYLL/ for the retained license and notice.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.ValuationUnitsToFieldUnits

/-!
# Coercion target for the canonical valuation-unit inclusion

This focused extraction states M335.016 from the pinned NYLL source as a
proposition. See the paired Markdown for source correspondence and
modifications.
-/

noncomputable section

namespace Langlands.NYLL.LubinTate

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The packaged valuation-unit inclusion preserves the underlying field
element. -/
def standardLocalFieldValuationUnitsToFieldUnits_apply_coeStatement
    (u : (standardLocalField K).valuationSubringˣ) : Prop :=
  ((standardLocalFieldValuationUnitsToFieldUnits K u : Kˣ) : K) =
    (((u : (standardLocalField K).valuationSubringˣ) :
      (standardLocalField K).valuationSubring) : K)

end Langlands.NYLL.LubinTate

end
