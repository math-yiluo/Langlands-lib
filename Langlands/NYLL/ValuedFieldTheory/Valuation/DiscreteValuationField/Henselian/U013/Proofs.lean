/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 740, 16 November 2026: extract only the proof of M104.013
`HenselianDVF.valuationSubring_isDiscreteValuationRing` from
Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Henselian.lean
(lines 251–253) at commit fbd320cd8b1b06487c58227e92eb135794267709 into
Langlands.NYLL; import only the published Henselian.Statements module and
state the theorem as its `valuationSubring_isDiscreteValuationRingStatement`.
The source term `F.toDVF.valuationSubring_isDiscreteValuationRing` (the not
yet published M103.011) is replaced by that theorem's source body
`Valuation.valuationSubring_isDiscreteValuationRing F.valuation`
(Basic.lean, line 92), a Mathlib instance. The noncomputable section is
omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian.Statements

/-!
# The valuation ring of a Henselian DVF is a DVR (NYLL M104.013)

The valuation subring of the chosen rank-one discrete valuation underlying a
Henselian discretely valued field is a discrete valuation ring. Henselianity
plays no role.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField

universe u v

namespace HenselianDVF

variable {K : Type u} [Field K]

/-- The valuation subring of the henselian model is a discrete valuation ring. -/
theorem valuationSubring_isDiscreteValuationRing (F : HenselianDVF.{u, v} K) :
    valuationSubring_isDiscreteValuationRingStatement F :=
  Valuation.valuationSubring_isDiscreteValuationRing F.valuation

end HenselianDVF

end Langlands.NYLL.ValuationTheory.DiscreteValuationField
