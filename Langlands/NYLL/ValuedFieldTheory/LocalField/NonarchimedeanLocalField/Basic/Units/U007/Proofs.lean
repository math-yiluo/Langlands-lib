/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.Units.Statements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U004.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U006.Proofs

/-!
# NYLL M128.007: the normalized valuation of a quotient

Modified by Worker 5264, 15 November 2026: prove the published target
`IsNonarchimedeanLocalField.v_divStatement` (M128.007) by the source proof
of `IsNonarchimedeanLocalField.v_div` in
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean` at
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
begin the proof with `show` stating it unfolded, and state the published
`...Statement`-typed results `v_mul` (M128.004) and `v_inv` (M128.006),
specialized to `K`, as the local facts `hmul` and `hinv` used by the source
rewrite in place of `v_mul` and `v_inv`. Replace the source import by the
published statement and proof modules and omit the rest of the source file.
See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

namespace IsNonarchimedeanLocalField

open scoped ValuativeRel WithZero

/-- The normalized valuation of a quotient is the difference of the two valuations. -/
theorem v_div (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : Kˣ) :
    v_divStatement K x y := by
  show v K (Additive.ofMul (x / y)) =
    v K (Additive.ofMul x) - v K (Additive.ofMul y)
  have hmul : ∀ a b : Kˣ,
      v K (Additive.ofMul (a * b)) =
        v K (Additive.ofMul a) + v K (Additive.ofMul b) :=
    v_mul K
  have hinv : ∀ a : Kˣ,
      v K (Additive.ofMul a⁻¹) = -v K (Additive.ofMul a) :=
    v_inv K
  rw [div_eq_mul_inv, hmul, hinv, sub_eq_add_neg]

end IsNonarchimedeanLocalField

end

end Langlands.NYLL.LocalFieldTheory
