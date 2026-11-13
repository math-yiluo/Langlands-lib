/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 344, 2026-11-13: extract the type of M336.002 from
upstream commit fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued
definition, retaining the complete source telescope and its hypothesis.
Prefix the namespace with Langlands.NYLL, import the focused series
definition, omit the proof and defer the ext attribute to that proof,
and disable the unused-variable linter only on the target declaration.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Series.Definitions

/-!
# Extensionality target for Lubin--Tate series

This module states M336.002 without proving it.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

namespace LubinTateSeries

variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

set_option linter.unusedVariables false in
/-- Target for equality of packages whose underlying power series agree. -/
def extStatement {e e' : LubinTateSeries F π}
    (h : e.toPowerSeries = e'.toPowerSeries) : Prop :=
  e = e'

end LubinTateSeries

end Langlands.NYLL.LubinTate

end
