/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 413, 2026-11-14: extract only M335.015 (lines 229–234)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; prefix the
namespace with Langlands.NYLL, replace the six source imports by the two
focused published imports below, and replace the module overview. See the
paired Markdown for the complete modification record and licenses/NYLL/ for
the retained license and notice.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.IntegerUnitsEquiv
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U016.Definitions

/-!
# The canonical valuation-unit inclusion

This focused extraction contains M335.015 from the pinned NYLL source.
See the paired Markdown for source correspondence and modifications.
-/

noncomputable section

namespace Langlands.NYLL.LubinTate

open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Inclusion of packaged valuation-ring units into field units, expressed
through the canonical integer-ring identification. -/
noncomputable def standardLocalFieldValuationUnitsToFieldUnits :
    (standardLocalField K).valuationSubringˣ →* Kˣ :=
  (integerUnitsToFieldUnits K).comp
    (standardLocalFieldIntegerUnitsEquiv K).symm.toMonoidHom

end Langlands.NYLL.LubinTate

end
