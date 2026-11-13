/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 259, 13 November 2026:
Extract the proof of M129.009 (lines 101–107, with section context at
lines 20–30 and 63–65) from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Norm.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
Langlands.NYLL and prove the published closed statement with its independent
universes u and v and complete internal telescope. Keep the source proof
after introducing that telescope; retain only the target and required
Mathlib imports. See paired Markdown. The upstream LICENSE and NOTICE
are preserved in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm.U009.Statements
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Valuation.Integral

/-!
# Norms of valuation integers

The exact proof of NYLL M129.009 under the namespaced integrality class.
-/

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

/-- The norm of an element integral over the base valuation ring lies in the base valuation ring. -/
theorem algebraNorm_mem_integers_of_mem_integers.{u, v} :
    algebraNorm_mem_integers_of_mem_integersStatement.{u, v} := by
  intro K L _ _ _ _ _ _ x
  exact Valuation.Integers.mem_of_integral
    (Valuation.integer.integers (ValuativeRel.valuation K))
    (Algebra.isIntegral_norm K (LocalFieldTheory.ValuativeExtension.integer_isIntegral x))

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
