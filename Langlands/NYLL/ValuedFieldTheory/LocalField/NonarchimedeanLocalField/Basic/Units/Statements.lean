/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U016.Definitions

/-!
# Targets: the valuation of a quotient and injectivity of integer units into field units

Modified by Worker 5264, 15 November 2026: state the source theorems
M128.007 `IsNonarchimedeanLocalField.v_div` and M128.018
`IsNonarchimedeanLocalField.integerUnitsToFieldUnits_injective` of
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean` at
fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the names, replace the source import by the published modules of `v` and
`integerUnitsToFieldUnits`, keep the source universe, scoped opens, binders
and statements unchanged, and omit the proofs and the rest of the source
file. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

namespace IsNonarchimedeanLocalField

open scoped ValuativeRel WithZero

/-- Target: the normalized valuation of a quotient is the difference of the
two valuations. -/
def v_divStatement (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : Kˣ) : Prop :=
    v K (Additive.ofMul (x / y)) =
      v K (Additive.ofMul x) - v K (Additive.ofMul y)

/-- Target: the canonical inclusion of valuation-integer units into field
units is injective. -/
def integerUnitsToFieldUnits_injectiveStatement
    (K : Type u) [Field K] [ValuativeRel K] : Prop :=
    Function.Injective (integerUnitsToFieldUnits K)

end IsNonarchimedeanLocalField

end
end Langlands.NYLL.LocalFieldTheory
