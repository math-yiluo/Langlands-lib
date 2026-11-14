/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 330, 2026-11-14: extract only M374.002 (lines 44–49)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; qualify
the declaration and opened namespaces with Langlands.NYLL, replace both
upstream imports by the published local-field Basic.Definitions module,
and replace the module documentation. Retain the declaration's signature,
body, docstring and noncomputable modifier. The retained license and
notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions

/-!
# The chosen base uniformizer as a field unit

This module extracts M374.002 from
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/NormSubgroup.lean`.
-/

universe u v

namespace Langlands.NYLL.LubinTate

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The chosen base uniformizer, regarded as a nonzero field unit. -/
noncomputable def standardLubinTateBaseUniformizerUnit
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    Kˣ :=
  Units.mk0 (π : K) hπ.ne_zero

end Langlands.NYLL.LubinTate
