/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 231, 2026-11-16: extract only M391.009 (lines 121–127)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; qualify
the namespace and open command with Langlands.NYLL, replace the twelve
upstream imports by the two published dependencies below, rename the
unit term from u to a, omit the redundant outer noncomputable section,
and replace the module documentation. The retained license and notices
are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.NormSubgroup.BaseUniformizerUnit.Definitions
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer.IsUniformizerProof

/-!
# The changed uniformizer as a base-field unit

This module extracts exactly M391.009 from
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ChangedUniformizer.lean`.
-/

universe u v

namespace Langlands.NYLL.LubinTate

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The changed uniformizer, regarded as a nonzero base-field unit. -/
noncomputable def standardLubinTateChangedUniformizerUnit
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (a : F.valuationSubringˣ) :
    Kˣ :=
  standardLubinTateBaseUniformizerUnit
    (standardLubinTateChangedUniformizer_isUniformizer hπ a)

end Langlands.NYLL.LubinTate
