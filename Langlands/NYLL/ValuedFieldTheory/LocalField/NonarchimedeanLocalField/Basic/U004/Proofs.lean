/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 120, 13 November 2026:
Extract the proof of M128.004 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import only the Basic ValuationStatements module, and
prove the published closed proposition by introducing its seven binders
before the original `simp` call. Omit the source noncomputable section and
all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.ValuationStatements

/-!
# Multiplicativity of the normalized valuation

The normalized valuation turns products of field units into sums of integers.
-/

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

universe u

open scoped ValuativeRel WithZero

/-- The normalized valuation turns multiplication of field units into addition of integers. -/
theorem v_mul : v_mulStatement.{u} := by
  intro K _ _ _ _ x y
  simp [v, Valuation.map_mul, WithZero.unzero_mul, toAdd_mul]

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
