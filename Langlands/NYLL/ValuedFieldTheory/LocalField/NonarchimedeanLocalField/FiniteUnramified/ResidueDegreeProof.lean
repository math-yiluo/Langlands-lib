/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 4699, 2026-11-15: prove the published closed target of M161.003,
the theorem IsNonarchimedeanLocalField.unramifiedValuation_residue_finrank_eq_finrank
at lines 57–74 of Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteUnramified.lean
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709, under the same name
prefixed with Langlands.NYLL. The theorem's type is the published closed proposition,
so the source binders become an opening intro; the source proof (lines 66–74) is
otherwise unchanged except that its reference to M138.029 carries the Langlands.NYLL
prefix. It uses the Library proofs of M138.029 and M161.002, whose types are closed
propositions applied to K and L. The source docstring, which repeats one sentence,
keeps that sentence once. The source imports are replaced by the published statement
module and those two proof modules. The retained license and notices are in
licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.RamificationIndexProof
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.ResidueDegreeStatement
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension.RamificationResidueDegreeProof

/-!
# Residue degree of an unramified valued extension: proof

This module proves the published closed target for NYLL M161.003.
-/

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

universe u

open scoped ValuativeRel

/-- For an unramified valued extension, the residue-field degree equals the
field-extension degree. This proves the closed target for NYLL M161.003. -/
theorem unramifiedValuation_residue_finrank_eq_finrank :
    unramifiedValuation_residue_finrank_eq_finrankStatement.{u} := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ _
  have h :=
    Langlands.NYLL.LocalFieldTheory.maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank
      K L
  have hp : (𝓂[K] : Ideal 𝒪[K]) ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (IsLocalRing.maximalIdeal.isMaximal 𝒪[K])
      (IsDiscreteValuationRing.not_isField 𝒪[K])
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp,
    unramifiedValuation_ramificationIdx_eq_one K L, one_mul] at h
  exact h

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
