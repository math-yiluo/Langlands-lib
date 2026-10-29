/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 29 October 2026:
Extract M093.005 from Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/
NormQuotient.lean at fbd320cd8b1b06487c58227e92eb135794267709.
Add the Langlands.NYLL namespace prefix, import the published U004 module alone,
omit the unused universe v and all other declarations, and preserve the source
telescope, docstring and definition body.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U004.Definitions

/-!
# Canonical projection to the general norm quotient

The quotient homomorphism from base-field units to their classes modulo norms.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

/-- Defines `normClass`. -/
def normClass (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Kˣ →* NormQuotient K L := by
  change Kˣ →* Kˣ ⧸ localNormSubgroup K L
  let N := localNormSubgroup K L
  exact QuotientGroup.mk' N

end

end Langlands.NYLL.LocalFieldTheory
