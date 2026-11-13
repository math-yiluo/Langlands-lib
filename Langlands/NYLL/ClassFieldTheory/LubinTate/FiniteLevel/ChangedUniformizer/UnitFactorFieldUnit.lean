/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 319, 2026-11-13: extract only M391.007 (lines 106–109)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; qualify
the declaration and referenced NYLL namespaces with Langlands.NYLL,
replace the twelve source imports by the two focused published imports
below, omit the surrounding noncomputable section while retaining the
explicit modifier, and replace the module overview. See the paired
Markdown for the complete modification record and licenses/NYLL/ for
the retained license and notice.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuationSubringUnitMap.Definitions

/-!
# A valuation-ring unit as a field unit

This focused extraction contains M391.007 from the pinned NYLL source.
See the paired Markdown for source correspondence and modifications.
-/

universe u v

namespace Langlands.NYLL.LubinTate

variable {K : Type u} [Field K]

/-- A valuation-ring unit regarded as a unit of the base field. -/
noncomputable def standardLubinTateUnitFactorFieldUnit
    (F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K)
    (u : F.valuationSubringˣ) : Kˣ :=
  Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits
    F.toCompleteDVF u

end Langlands.NYLL.LubinTate
