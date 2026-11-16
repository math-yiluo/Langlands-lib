/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Statements

/-!
# NYLL M107.032: the maximal ideal of a complete DVF is nonzero

Modified by Worker 5264, 15 November 2026: prove the published target
`CompleteDVF.maximalIdeal_ne_botStatement` (M107.032) by the source proof of
`CompleteDVF.maximalIdeal_ne_bot` in
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Complete.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
begin the proof with `show` stating it unfolded, replace the source uses of
`F.exists_uniformizer` (M107.022) and `F.uniformizer_mem_maximalIdeal hpi`
(M107.023), which are not yet published, by local `have`s `hex` and `hunif`
proved by the source bodies of the underlying DVF theorems (M103.020,
M103.021) through Mathlib,
replace the source imports by the published statement module and omit the universe
`w` and the rest of the source file. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ValuationTheory

noncomputable section

universe u v

namespace DiscreteValuationField

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- The maximal ideal of a complete DVF valuation ring is nonzero. -/
theorem maximalIdeal_ne_bot (F : CompleteDVF.{u, v} K) :
    maximalIdeal_ne_botStatement F := by
  show F.maximalIdeal ≠ ⊥
  have hex :
      Exists (fun pi : F.valuationSubring => F.valuation.IsUniformizer (pi : K)) :=
    _root_.Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial F.valuation
  have hunif : ∀ {pi : F.valuationSubring},
      F.valuation.IsUniformizer (pi : K) → pi ∈ F.maximalIdeal := fun hpi =>
    (_root_.Valuation.mem_maximalIdeal_iff (v := F.valuation)).2 hpi.val_lt_one
  rcases hex with ⟨pi, hpi⟩
  intro hbot
  have hmem : pi ∈ (⊥ : Ideal F.valuationSubring) := by
    rw [← hbot]
    exact hunif hpi
  have hzero_sub : pi = 0 := by
    simpa using hmem
  apply hpi.ne_zero
  exact Subtype.ext_iff.mp hzero_sub

end CompleteDVF

end DiscreteValuationField

end

end Langlands.NYLL.ValuationTheory
