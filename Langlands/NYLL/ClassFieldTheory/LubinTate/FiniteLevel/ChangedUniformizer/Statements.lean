/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 231, 2026-11-14: extract only the proposition of
M391.003 (lines 69–76) at upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 as an unproved closed Prop
definition; qualify the namespaces with Langlands.NYLL, replace the
upstream imports by the published changed-parameter definition module,
and replace the module documentation. The retained license and notices
are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer.Definitions

/-!
# Changed-uniformizer preservation target

The proposition of source unit M391.003, stated using the published
local-field package and changed-parameter definition. This module supplies
the target for a separate proof.
-/

universe u v

namespace Langlands.NYLL.LubinTate

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField

set_option linter.unusedVariables false in
/-- Target: multiplication by a valuation-ring unit preserves the uniformizer property. -/
def standardLubinTateChangedUniformizer_isUniformizerStatement : Prop :=
  ∀ {K : Type u} [Field K] {F : LocalField.{u, v} K}
    {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ),
    F.toCompleteDVF.valuation.IsUniformizer
      (standardLubinTateChangedUniformizer F π u : K)

end Langlands.NYLL.LubinTate
