/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.Units.Statements

/-!
# NYLL M128.018: injectivity of integer units into field units

Modified by Worker 5264, 15 November 2026: prove the published target
`IsNonarchimedeanLocalField.integerUnitsToFieldUnits_injectiveStatement`
(M128.018) by the source proof of
`IsNonarchimedeanLocalField.integerUnitsToFieldUnits_injective` in
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean` at
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
begin the proof with `show` stating it unfolded, replace the source import
by the published statement module and omit the rest of the source file. See
the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

namespace IsNonarchimedeanLocalField

open scoped ValuativeRel WithZero

/-- The canonical inclusion of valuation-integer units into field units is
injective. -/
theorem integerUnitsToFieldUnits_injective
    (K : Type u) [Field K] [ValuativeRel K] :
    integerUnitsToFieldUnits_injectiveStatement K := by
  show Function.Injective (integerUnitsToFieldUnits K)
  intro x y hxy
  apply Units.ext
  apply Subtype.ext
  simpa [integerUnitsToFieldUnits] using congrArg Units.val hxy

end IsNonarchimedeanLocalField

end

end Langlands.NYLL.LocalFieldTheory
