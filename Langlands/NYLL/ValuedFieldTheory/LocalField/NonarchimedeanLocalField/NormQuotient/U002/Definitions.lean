/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 248, 27 October 2026:
Extract M093.002 from Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/
NormQuotient.lean at fbd320cd8b1b06487c58227e92eb135794267709.
Add the Langlands.NYLL namespace prefix, import the published
localNormSubgroup definition alone, omit the unused universe v and all other
declarations, and preserve the source telescope and definition body.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U001.Definitions

/-!
# General norm quotient

Base-field units modulo the norm image subgroup, without a finiteness assumption.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

/-- Units modulo field norms. -/
def NormQuotient (K L : Type u) [Field K] [Field L] [Algebra K L] : Type u :=
  Kˣ ⧸ localNormSubgroup K L

end

end Langlands.NYLL.LocalFieldTheory
