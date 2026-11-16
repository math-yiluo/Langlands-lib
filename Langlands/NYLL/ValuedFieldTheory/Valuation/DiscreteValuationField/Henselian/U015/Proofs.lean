/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 740, 16 November 2026: extract only the proof of M104.015
`HenselianDVF.maximalIdeal_ne_bot` from
Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Henselian.lean
(lines 262–264) at commit fbd320cd8b1b06487c58227e92eb135794267709 into
Langlands.NYLL; import only the published Henselian.Statements module and
state the theorem as its `maximalIdeal_ne_botStatement`. The source term
`F.toDVF.maximalIdeal_ne_bot` (the not yet published M103.030, proved in the
source from a uniformizer) is replaced by Mathlib's
`IsDiscreteValuationRing.not_a_field` for the Mathlib DVR instance
`Valuation.valuationSubring_isDiscreteValuationRing F.valuation` (the source
body of M103.011, Basic.lean, line 92). The noncomputable section is omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian.Statements

/-!
# The maximal ideal of a Henselian DVF is nonzero (NYLL M104.015)

The maximal ideal of the valuation subring of a Henselian discretely valued
field is not the zero ideal, because that valuation subring is a discrete
valuation ring, hence not a field. Henselianity plays no role.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField

universe u v

namespace HenselianDVF

variable {K : Type u} [Field K]

/-- The maximal ideal of a Henselian DVF valuation ring is nonzero. -/
theorem maximalIdeal_ne_bot (F : HenselianDVF.{u, v} K) :
    maximalIdeal_ne_botStatement F :=
  haveI : IsDiscreteValuationRing F.valuationSubring :=
    Valuation.valuationSubring_isDiscreteValuationRing F.valuation
  IsDiscreteValuationRing.not_a_field F.valuationSubring

end HenselianDVF

end Langlands.NYLL.ValuationTheory.DiscreteValuationField
