/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Statements

/-!
# NYLL M107.013: the valuation subring of a complete DVF is a discrete valuation ring

Modified by Worker 5264, 15 November 2026: prove the published target
`CompleteDVF.valuationSubring_isDiscreteValuationRingStatement` (M107.013)
following the source proof of
`CompleteDVF.valuationSubring_isDiscreteValuationRing` in
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Complete.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
begin the proof with `show` stating it unfolded, replace the source term
`F.toDVF.valuationSubring_isDiscreteValuationRing` (the unpublished M103.011)
by its own source body, the Mathlib instance
`Valuation.valuationSubring_isDiscreteValuationRing F.valuation`, after a
`change` to the valuation subring of `F.valuation`,
replace the source imports by the published statement module and omit the universe
`w` and the rest of the source file. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ValuationTheory

noncomputable section

universe u v

namespace DiscreteValuationField

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- The valuation subring in the complete model is a discrete valuation ring. -/
theorem valuationSubring_isDiscreteValuationRing (F : CompleteDVF.{u, v} K) :
    valuationSubring_isDiscreteValuationRingStatement F := by
  show IsDiscreteValuationRing F.valuationSubring
  change IsDiscreteValuationRing F.valuation.valuationSubring
  exact _root_.Valuation.valuationSubring_isDiscreteValuationRing F.valuation

end CompleteDVF

end DiscreteValuationField

end

end Langlands.NYLL.ValuationTheory
