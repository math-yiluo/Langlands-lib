/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 326, 2026-11-14: extract the signature of M354.012
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
# Closure of intertwining under one-variable composition

The exact proposition target for source unit M354.012.
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

namespace Intertwines

/-- Exact target of M354.012: one-variable outer composition with a
multivariable intertwiner preserves the intertwining equation. -/
abbrev powerSeries_substStatement
    [Finite τ]
    {e ebar ehat : LubinTateSeries F π}
    {H : PowerSeries F.valuationSubring}
    (hH : Intertwines e ebar H)
    (hHsubst : PowerSeries.HasSubst H)
    {G : MvPowerSeries τ F.valuationSubring}
    (hG : Intertwines ebar ehat G)
    (hGsubst : PowerSeries.HasSubst G) : Prop :=
  Intertwines e ehat (PowerSeries.subst G H)

end Intertwines

end SameUniformizer
end Langlands.NYLL.LubinTate
