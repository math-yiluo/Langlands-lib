/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 318, 2026-11-13: extract only M391.001 (lines 52–57)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; qualify
the namespace and open command with Langlands.NYLL, replace the upstream
imports by the focused shared LocalField definition module, and replace
the module documentation by the scope of this extraction. The retained
license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions

/-!
# Unit multiplication in a local field's valuation ring

This module extracts the changed-parameter definition from
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ChangedUniformizer.lean`.
The construction takes any valuation-ring element and a valuation-ring unit.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The unit change `uπ` of a chosen integral uniformizer. -/
def standardLubinTateChangedUniformizer
    (F : LocalField.{u, v} K) (π : F.valuationSubring)
    (u : F.valuationSubringˣ) :
    F.valuationSubring :=
  (u : F.valuationSubring) * π

end Langlands.NYLL.LubinTate

end
