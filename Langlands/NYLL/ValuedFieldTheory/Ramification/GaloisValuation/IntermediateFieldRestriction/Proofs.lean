/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 89, 13 November 2026: the proof of the source theorem
RamificationTheory.intermediateFieldRestrictNormalHom_apply_val (inventory M259.002),
stated as Langlands.NYLL.RamificationTheory.intermediateFieldRestrictNormalHom_apply_val
for the published target intermediateFieldRestrictNormalHom_apply_valStatement.
The universes, section variables, telescope and tactic proof are unchanged; the
conclusion is the published target applied to the telescope.
Prepared by Worker 307, 13 November 2026, from Worker 89's shared draft:
retained the proof unchanged and expanded the paired documentation.
The retained license and notice are licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction.Statements

/-!
# Evaluation of the intermediate-field restriction: proof

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ValuedFieldTheory/Ramification/GaloisValuation/IntermediateFieldRestriction.lean`,
lines 38–49 (inventory M259.002).
-/

noncomputable section

namespace Langlands.NYLL.RamificationTheory

universe u v

variable {K : Type u} {Omega : Type v}
  [Field K] [Field Omega] [Algebra K Omega]

/-- Evaluation of the canonical intermediate-field restriction after both
sides are included in the common ambient field. -/
theorem intermediateFieldRestrictNormalHom_apply_val
    (E F : IntermediateField K Omega) (hEF : E ≤ F) [Normal K E]
    (sigma : F ≃ₐ[K] F) (x : E) :
    intermediateFieldRestrictNormalHom_apply_valStatement E F hEF sigma x := by
  let : Algebra E F :=
    RingHom.toAlgebra (IntermediateField.inclusion hEF).toRingHom
  let : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  have h := AlgEquiv.restrictNormal_commutes sigma E x
  exact congrArg F.val h

end Langlands.NYLL.RamificationTheory
