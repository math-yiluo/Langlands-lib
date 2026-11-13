/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Statements

/-!
# Subgroup inclusion reverses inclusion of abstract fixed fields

Adapted by Worker 213 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, unit M099.006.
The paired Markdown records the extraction and modifications.
Original license and notices: `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

omit [IsGalois k Ω] in
/-- Inclusion of abstract subgroups reverses inclusion of their concrete fixed fields. -/
theorem abstractFixedField_le {K L : ClosedSubgroup (Gal(Ω/k))}
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    abstractFixedField_leStatement k Ω hLK :=
  IntermediateField.fixedField_le hLK

end
end Langlands.NYLL.LocalClassFieldTheory
