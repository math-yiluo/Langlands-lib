/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 341, 2026-11-13: extract the M266.003 proof from
commit fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL, prove the published closed proposition target, replace
the source imports with the target and valuation-surjectivity modules,
and use definitional evaluation in place of the source simp lemma.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.AdditiveStatements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U005.Proofs

namespace Langlands.NYLL.LocalClassFieldTheory

/-- The normalized valuation remains surjective after reduction modulo any natural degree. -/
theorem valuationModDegree_surjective.{u} :
    valuationModDegree_surjectiveStatement.{u} := by
  intro K _ _ _ _ n z
  rcases ZMod.intCast_surjective z with ⟨m, rfl⟩
  rcases LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_surjective K m with
    ⟨x, hx⟩
  refine ⟨x, ?_⟩
  change (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K x : ZMod n) =
    (m : ZMod n)
  rw [hx]

end Langlands.NYLL.LocalClassFieldTheory
