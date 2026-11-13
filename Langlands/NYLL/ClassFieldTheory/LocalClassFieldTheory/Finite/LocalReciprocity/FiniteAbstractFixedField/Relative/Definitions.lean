/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions

/-!
# Scalar extension of abstract fixed fields

Adapted by Worker 203 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
See the paired Markdown for the declaration map and complete modification record.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory
noncomputable section
variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
/-- The upper fixed field, regarded as an intermediate field over the lower
fixed field in a relative abstract extension. -/
abbrev abstractRelativeFixedField
    {K L : ClosedSubgroup (Gal(Ω/k))}
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    IntermediateField (abstractFixedField k Ω K) Ω :=
  IntermediateField.extendScalars (IntermediateField.fixedField_le hLK)
end
end Langlands.NYLL.LocalClassFieldTheory
