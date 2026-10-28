/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 248, 28 October 2026:
Extract M093.003 from Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/
NormQuotient.lean at fbd320cd8b1b06487c58227e92eb135794267709.
Add the Langlands.NYLL namespace prefix, import the published NormQuotient
definition alone, omit the unused universe v and all other declarations,
and preserve the source telescope and instance body.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U002.Definitions

/-!
# Group structure on the general norm quotient

The commutative quotient-group structure on base-field units modulo norms.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

/-- Field units modulo the local norm subgroup form a commutative group. -/
instance normQuotientCommGroup (K L : Type u) [Field K] [Field L] [Algebra K L] :
    CommGroup (NormQuotient K L) := by
  change CommGroup (Kˣ ⧸ localNormSubgroup K L)
  infer_instance

end

end Langlands.NYLL.LocalFieldTheory
