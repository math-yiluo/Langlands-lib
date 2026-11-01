/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 1 November 2026:
Extract M093.023 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published U022 Proofs module.
Preserve the original telescope, result, docstring and quotient-descent
body. Retain the shared universe u and noncomputable section, omitting
the unused universe v and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U022.Proofs

/-!
# Norm quotient map induced by norm subgroup inclusion

The identity on base-field units descends from the quotient by a smaller
norm subgroup to the quotient by a larger norm subgroup.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

/-- The map of norm quotients induced by inclusion of their norm subgroups. -/
def normQuotientMapOfLE
    (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (h : localNormSubgroup K L ≤ localNormSubgroup K M) :
    NormQuotient K L →* NormQuotient K M :=
  normQuotientLift (normClass K M) fun x hx =>
    (normClass_eq_one_iff_mem K M x).2 (h hx)

end

end Langlands.NYLL.LocalFieldTheory
