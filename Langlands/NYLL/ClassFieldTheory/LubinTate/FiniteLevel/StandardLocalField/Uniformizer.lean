/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 412, 2026-11-14: extract only M335.019 (lines 284–289)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; prefix the
namespace with Langlands.NYLL, replace the six source imports by the
published standard integer-ring equivalence and chosen-uniformizer modules,
keep only the opened namespace the extracted unit uses, and replace the
module documentation. See the paired Markdown for the complete record.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.IntegerEquiv
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.Definitions

/-!
# The transported canonical uniformizer

The chosen irreducible element `chosenIntegerRingUniformizer K` of the
topology-first integer ring `𝒪[K]`, transported along
`standardLocalFieldIntegerEquiv K` to the valuation subring of the canonical
local-field package `standardLocalField K`. Extracted from
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean`.
-/

noncomputable section

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The canonical chosen uniformizer of `𝒪[K]`, transported to the
valuation ring of the standard local-field package. -/
noncomputable def standardLocalFieldUniformizer :
    (standardLocalField K).valuationSubring :=
  standardLocalFieldIntegerEquiv K
    (chosenIntegerRingUniformizer K)

end Langlands.NYLL.LubinTate
