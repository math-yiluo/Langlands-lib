/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 526, 2026-11-14: extract M266.002 from commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL, import the published AdditiveStatements target, and
state the theorem with exactly that closed proposition as its type.
Introduce its original telescope and retain the source rfl proof.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.AdditiveStatements

/-!
# Evaluation of the normalized valuation modulo a degree

Exact proof of the published M266.002 target, adapted from source lines 37–41.
-/

universe u

namespace Langlands.NYLL.LocalClassFieldTheory

/-- Evaluates the normalized valuation map after reduction modulo `n`. -/
@[simp]
theorem valuationModDegree_apply : valuationModDegree_applyStatement.{u} := by
  intro K _ _ _ _ n x
  rfl

end Langlands.NYLL.LocalClassFieldTheory
