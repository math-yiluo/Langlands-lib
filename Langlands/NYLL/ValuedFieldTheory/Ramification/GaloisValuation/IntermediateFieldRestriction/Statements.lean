/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 30, 13 November 2026: extracted the source theorem
RamificationTheory.intermediateFieldRestrictNormalHom_apply_val (inventory M259.002)
as the Prop-valued target
Langlands.NYLL.RamificationTheory.intermediateFieldRestrictNormalHom_apply_valStatement.
The source proof is omitted. The universes, section variables and telescope are
unchanged; the only import is the published adapted definition M259.001.
The retained license and notice are licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction.Definitions

/-!
# Evaluation of the intermediate-field restriction: statement target

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ValuedFieldTheory/Ramification/GaloisValuation/IntermediateFieldRestriction.lean`,
lines 38–44 (inventory M259.002).
-/

noncomputable section

namespace Langlands.NYLL.RamificationTheory

universe u v

variable {K : Type u} {Omega : Type v}
  [Field K] [Field Omega] [Algebra K Omega]

/-- Evaluation of the canonical intermediate-field restriction after both
sides are included in the common ambient field. -/
def intermediateFieldRestrictNormalHom_apply_valStatement
    (E F : IntermediateField K Omega) (hEF : E ≤ F) [Normal K E]
    (sigma : F ≃ₐ[K] F) (x : E) : Prop :=
  E.val (intermediateFieldRestrictNormalHom E F hEF sigma x) =
    F.val (sigma (IntermediateField.inclusion hEF x))

end Langlands.NYLL.RamificationTheory
