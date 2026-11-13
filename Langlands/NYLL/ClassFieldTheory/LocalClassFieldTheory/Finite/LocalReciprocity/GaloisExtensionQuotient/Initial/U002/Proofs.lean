/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.Statements

/-!
# Fixing subgroups lie in the base fixing subgroup

Adapted by Worker 213 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, unit M089.002.
The paired Markdown records the extraction and modifications.
Original license and notices: `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory

noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- The fixing subgroup of an intermediate field lies in the base fixing subgroup. -/
theorem fixingSubgroupLeBase (E : IntermediateField K Ω) :
    fixingSubgroupLeBaseStatement K Ω E :=
  IntermediateField.fixingSubgroup_le bot_le

end
end Langlands.NYLL.LocalClassFieldTheory
