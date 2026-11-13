/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.Statements

/-!
# The bottom fixing subgroup is the abstract base field

Adapted by Worker 213 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, unit M089.001.
The paired Markdown records the extraction and modifications.
Original license and notices: `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory ClassFormation

noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- The subgroup fixing the bottom intermediate field is the distinguished base field. -/
theorem closedFixingSubgroup_bot_eq_baseField :
    closedFixingSubgroup_bot_eq_baseFieldStatement K Ω := by
  ext σ
  change σ ∈ (⊥ : IntermediateField K Ω).fixingSubgroup ↔
    σ ∈ (⊤ : Subgroup (Gal(Ω / K)))
  rw [IntermediateField.fixingSubgroup_bot]

end
end Langlands.NYLL.LocalClassFieldTheory
