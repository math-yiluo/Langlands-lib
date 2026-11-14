/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 356, 2026-11-14: extract the signature and conclusion of
M353.045, source lines 1004–1011 at commit
fbd320cd8b1b06487c58227e92eb135794267709, as a Prop-valued Statement
abbreviation. Prefix the namespace with Langlands.NYLL and replace the
source imports by the published linear-term and intertwining definitions.
Retain all source parameters, names and hypotheses in their source order.
Suppress unused-variable linting for the hypotheses retained by this target.
The source proof is reserved for a separate exact proof successor. The
original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.Definitions
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions

/-!
# Equality of same-uniformizer intertwiners with a fixed linear term

This is the exact proposition target of M353.045. Two series satisfying the
same intertwining equation and the same prescribed linear term are equal.
-/

universe u v w

namespace Langlands.NYLL.LubinTate.SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {pi : F.valuationSubring}
variable {sigma : Type w} [Fintype sigma]

set_option linter.unusedVariables false in
/-- Target of M353.045: two same-uniformizer intertwiners with the same
prescribed linear term are equal. -/
abbrev eq_of_hasLinearTerm_of_intertwinesStatement
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring)
    {H H' : MvPowerSeries sigma F.valuationSubring}
    (hH : HasLinearTerm H L) (hI : Intertwines e ebar H)
    (hH' : HasLinearTerm H' L) (hI' : Intertwines e ebar H') : Prop :=
  H = H'

end Langlands.NYLL.LubinTate.SameUniformizer
