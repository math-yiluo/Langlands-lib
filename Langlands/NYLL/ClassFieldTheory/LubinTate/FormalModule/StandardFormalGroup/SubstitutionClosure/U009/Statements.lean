/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 326, 2026-11-14: extract the signature of M354.009
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709 as a
Prop-valued abbrev with the suffix Statement; prefix the namespace with
Langlands.NYLL, use focused published imports, omit the source proof and
unrelated declarations, and focus the module documentation. Preserve all
source binders and hypotheses; disable only the unused-variable linter
because a proposition target need not use its retained proof arguments.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions

/-!
# Substitution into an inserted variable

The exact proposition target for source unit M354.009.
-/

universe u v w w'

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w}
variable {τ : Type w'}

set_option linter.unusedVariables false

/-- Exact target of M354.009: substitution into `e(X_i)` evaluates `e`
at the corresponding member of the substituted family. -/
abbrev subst_inVariableStatement
    (e : LubinTateSeries F π)
    {G : σ → MvPowerSeries τ F.valuationSubring}
    (hG : MvPowerSeries.HasSubst G) (i : σ) : Prop :=
  MvPowerSeries.subst G (inVariable e i) =
    PowerSeries.subst (G i) e.toPowerSeries

end SameUniformizer
end Langlands.NYLL.LubinTate
