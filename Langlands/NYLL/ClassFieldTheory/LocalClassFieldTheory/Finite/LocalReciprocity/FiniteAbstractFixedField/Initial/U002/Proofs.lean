/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Statements

/-!
# Recovering a closed subgroup from its abstract fixed field

Adapted by Worker 213 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, unit M099.002.
The paired Markdown records the extraction and modifications.
Original license and notices: `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory

noncomputable section

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- Taking the closed fixing subgroup of an abstract fixed field recovers its subgroup. -/
theorem closedFixingSubgroup_abstractFixedField_eq
    (H : ClosedSubgroup (Gal(Ω/k))) :
    closedFixingSubgroup_abstractFixedField_eqStatement k Ω H := by
  ext σ
  change σ ∈ (abstractFixedField k Ω H).fixingSubgroup ↔ σ ∈ H
  rw [InfiniteGalois.fixingSubgroup_fixedField H]
  rfl

end
end Langlands.NYLL.LocalClassFieldTheory
