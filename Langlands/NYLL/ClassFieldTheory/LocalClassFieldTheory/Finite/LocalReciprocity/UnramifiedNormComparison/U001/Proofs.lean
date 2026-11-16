/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 396, 2026-11-15: prove the published closed target of M267.001,
the theorem LocalClassFieldTheory.localNormSubgroup_le_unramifiedNormSubgroup at
lines 47–59 of Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709, under the same name
prefixed with Langlands.NYLL. The theorem's type is the published closed proposition,
so the source section variables are introduced in the proof's opening intro together
with the source's x hx (line 50). The rest of the source proof (lines 51–59) is
unchanged, except that its call of v_normUnits_eq_residue_finrank_mul_of_isGalois K L
(M162.025, whose proof is not in the Library) is replaced by
v_normUnits_eq_residue_finrank_mul_of_isSeparable K L (M162.019), whose application
to x is the source proof of M162.025. It uses the Library proofs of M266.012,
M134.004, M162.019 and M161.003. The source docstring is kept and one sentence
naming the target is added. The source imports are replaced by the
published statement module and those four proof modules, and the source's
noncomputable section is omitted. The retained license and notices are in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormComparison.SubgroupStatements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U012.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U004.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation.U019.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.ResidueDegreeProof

/-!
# Field norms lie in the unramified norm subgroup: proof

This module proves the published closed target for NYLL M267.001.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- Every field norm has normalized valuation divisible by the degree. This proves
the closed target for NYLL M267.001. -/
theorem localNormSubgroup_le_unramifiedNormSubgroup :
    localNormSubgroup_le_unramifiedNormSubgroupStatement := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x hx
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
  apply (mem_unramifiedNormSubgroup_iff K (Module.finrank K L) _).2
  rw [valuationMap_apply]
  change (Module.finrank K L : Int) ∣
    v K (Additive.ofMul
      (LocalFieldTheory.normUnits K L y))
  rw [v_normUnits_eq_residue_finrank_mul_of_isSeparable K L,
    unramifiedValuation_residue_finrank_eq_finrank K L]
  exact dvd_mul_right _ _

end Langlands.NYLL.LocalClassFieldTheory
