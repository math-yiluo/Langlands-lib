/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 530, 2026-11-14: extract M266.007 from commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL, prove the exact closed published Statement target by
introducing its telescope before the original rfl proof, and replace the
source imports by the focused published target. Retain the simp attribute.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.MultiplicativeStatements

/-!
# Evaluation of the multiplicative valuation modulo degree

Source: M266.007, lines 78–83 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`.
-/

universe u

namespace Langlands.NYLL.LocalClassFieldTheory

/-- Evaluates the multiplicative form of the valuation-modulo-degree map. -/
@[simp]
theorem valuationModDegreeMulHom_apply :
    valuationModDegreeMulHom_applyStatement.{u} := by
  intro K _ _ _ _ n x
  rfl

end Langlands.NYLL.LocalClassFieldTheory
