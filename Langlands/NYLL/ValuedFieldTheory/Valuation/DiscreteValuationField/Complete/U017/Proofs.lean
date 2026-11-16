/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Statements

/-!
# NYLL M107.017: membership in the valuation subring of a complete DVF

Modified by Worker 5264, 15 November 2026: prove the published target
`CompleteDVF.mem_valuationSubring_iffStatement` (M107.017) following the
source proof of `CompleteDVF.mem_valuationSubring_iff` in
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Complete.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
replace the source term `F.toDVF.mem_valuationSubring_iff x` (the unpublished
M103.015) by its own source body, the Mathlib theorem
`Valuation.mem_valuationSubring_iff (v := F.valuation) x`,
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

/-- Membership in the valuation subring is characterized by nonnegative valuation. -/
theorem mem_valuationSubring_iff (F : CompleteDVF.{u, v} K) (x : K) :
    mem_valuationSubring_iffStatement F x :=
  _root_.Valuation.mem_valuationSubring_iff (v := F.valuation) x

end CompleteDVF

end DiscreteValuationField

end

end Langlands.NYLL.ValuationTheory
