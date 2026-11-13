/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Statements

/-!
# Evaluation of the abstract subgroup Galois equivalence

Adapted by Worker 213 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, unit M099.008.
The paired Markdown records the extraction and modifications.
Original license and notices: `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- The subgroup Galois equivalence preserves evaluation on the ambient field. -/
@[simp]
theorem abstractSubgroupEquivGaloisGroup_apply
    (H : ClosedSubgroup (Gal(Ω/k))) (σ : H.toSubgroup) (x : Ω) :
    abstractSubgroupEquivGaloisGroup_applyStatement k Ω H σ x :=
  rfl

end
end Langlands.NYLL.LocalClassFieldTheory
