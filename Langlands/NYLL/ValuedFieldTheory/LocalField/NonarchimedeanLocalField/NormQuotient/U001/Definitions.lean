/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 583, 26 October 2026:
Extract M093.001 from Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/
NormQuotient.lean at fbd320cd8b1b06487c58227e92eb135794267709.
Add the Langlands.NYLL namespace prefix, import the published normUnits
definition alone, omit the unused universe v and all later declarations,
and preserve the source telescope and definition body.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions

/-!
# General norm image subgroup

The image of the algebra norm on unit groups, without a finiteness assumption.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

/-- The norm subgroup N_{L/K}(Lˣ) ≤ Kˣ. -/
def localNormSubgroup (K L : Type u) [Field K] [Field L] [Algebra K L] : Subgroup Kˣ :=
  (normUnits K L).range

end

end Langlands.NYLL.LocalFieldTheory
