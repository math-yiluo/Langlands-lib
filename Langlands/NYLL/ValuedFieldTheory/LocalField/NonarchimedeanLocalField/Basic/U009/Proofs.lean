/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 105, 14 November 2026:
Extract the proof of M128.009 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import the Basic PowValuationStatements module and the
published proofs of v_inv (M128.006) and v_pow (M128.008), and prove the
published closed proposition by introducing its seven binders before the
original case split. The source theorems `v_pow` and `v_inv` are used through
the published proofs as `v_pow K` and `v_inv K`. Omit the source
noncomputable section and all other source declarations, and state the
duplicated source docstring sentence once.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.PowValuationStatements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U006.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U008.Proofs

/-!
# Normalized valuation of integral powers

The normalized valuation of an integral power of a field unit is that integer times the
normalized valuation of the unit.
-/

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

universe u

open scoped ValuativeRel WithZero

/-- Raising a field unit to an integral power multiplies its normalized valuation by that
integer. -/
theorem v_zpow : v_zpowStatement.{u} := by
  intro K _ _ _ _ x n
  cases n with
  | ofNat n =>
      simpa using v_pow K x n
  | negSucc n =>
      rw [zpow_negSucc, v_inv K, v_pow K]
      change -(((n + 1 : Nat) : Int) * v K (Additive.ofMul x)) =
        (-(((n + 1 : Nat) : Int))) * v K (Additive.ofMul x)
      ring

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
