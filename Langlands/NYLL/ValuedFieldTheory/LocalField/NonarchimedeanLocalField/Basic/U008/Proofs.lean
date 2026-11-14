/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 105, 14 November 2026:
Extract the proof of M128.008 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import the Basic PowValuationStatements module and the
published proofs of v_mul (M128.004) and v_one (M128.005), and prove the
published closed proposition by introducing its seven binders before the
original induction. The source theorems `v_one` and `v_mul` are used through
the published proofs as `v_one K` and `v_mul K`. Omit the source
noncomputable section and all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.PowValuationStatements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U004.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U005.Proofs

/-!
# Normalized valuation of natural powers

The normalized valuation of a natural power of a field unit is that power times the
normalized valuation of the unit.
-/

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

universe u

open scoped ValuativeRel WithZero

/-- Raising a field unit to a natural power multiplies its normalized valuation by that power. -/
theorem v_pow : v_powStatement.{u} := by
  intro K _ _ _ _ x n
  induction n with
  | zero =>
      rw [pow_zero, v_one K, Nat.cast_zero, zero_mul]
  | succ n ih =>
      rw [pow_succ, v_mul K, ih]
      rw [show ((n + 1 : Nat) : Int) = (n : Int) + 1 from Nat.cast_add_one n]
      ring

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
