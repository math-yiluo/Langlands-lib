/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.Statements

/-!
# Surjectivity of the base-to-ambient quotient map

Adapted by Worker 213 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, unit M089.008.
The paired Markdown records the extraction and modifications.
Original license and notices: `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory

noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- Every ambient quotient class comes from the base fixing group. -/
theorem baseFixingToAmbientQuotient_surjective
    (E : IntermediateField K Ω) [IsGalois K E] :
    baseFixingToAmbientQuotient_surjectiveStatement K Ω E := by
  intro q
  refine Quotient.inductionOn' q ?_
  intro σ
  have hσ :
      σ ∈ (closedFixingSubgroup K Ω
        (⊥ : IntermediateField K Ω)).toSubgroup := by
    change σ ∈ (⊥ : IntermediateField K Ω).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_bot]
    exact Subgroup.mem_top σ
  exact ⟨⟨σ, hσ⟩, rfl⟩

end
end Langlands.NYLL.LocalClassFieldTheory
