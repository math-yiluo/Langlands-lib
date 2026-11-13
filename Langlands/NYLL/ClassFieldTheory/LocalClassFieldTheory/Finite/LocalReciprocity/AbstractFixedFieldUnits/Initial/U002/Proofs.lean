/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Initial.Statements

/-!
# Projection of the fixed-field unit equivalence

Adapted by Worker 213 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, unit M101.002.
The paired Markdown records the extraction and modifications.
Original license and notices: `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

omit [IsGalois k Ω] in
/-- The fixed-field unit equivalence projects to the ambient unit inclusion. -/
@[simp]
theorem abstractFixedFieldUnitsEquivGaloisFixed_coe
    (H : ClosedSubgroup (Gal(Ω/k)))
    (x : Additive (abstractFixedField k Ω H)ˣ) :
    abstractFixedFieldUnitsEquivGaloisFixed_coeStatement k Ω H x :=
  rfl

end
end Langlands.NYLL.LocalClassFieldTheory
