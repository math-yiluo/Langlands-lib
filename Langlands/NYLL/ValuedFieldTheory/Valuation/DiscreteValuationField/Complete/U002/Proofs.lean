/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Statements

/-!
# NYLL M107.002: adic completeness of the valuation subring of a complete discrete valuation

Modified by Worker 5264, 15 November 2026: prove the published target
`Valuation.isAdicCompleteStatement` (M107.002) by the source proof of
`Valuation.isAdicComplete` in
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Complete.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
replace the source imports by the published statement module and omit the universe
`w` and the rest of the source file. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ValuationTheory

noncomputable section

universe u v

namespace DiscreteValuationField

namespace Valuation

variable {K : Type u} [Field K]
variable {Gamma : Type v} [LinearOrderedCommGroupWithZero Gamma]

/-- Completeness of the valued field implies adic completeness of its valuation subring. -/
theorem isAdicComplete (val : _root_.Valuation K Gamma) [IsCompleteDiscrete val] :
    isAdicCompleteStatement val :=
  IsCompleteDiscrete.isAdicComplete (val := val)

end Valuation

end DiscreteValuationField

end

end Langlands.NYLL.ValuationTheory
