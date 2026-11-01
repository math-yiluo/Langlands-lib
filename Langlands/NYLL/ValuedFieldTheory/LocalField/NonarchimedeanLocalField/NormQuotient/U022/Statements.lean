/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 1 November 2026:
Extract the statement of M093.022 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and place all six source term binders of normClass_eq_one_iff_mem
inside a closed Prop-valued definition, preserving their order, binder
kinds, shared universe u and equivalence.
Import only the published U021 Proofs module. Omit the source proof,
noncomputable section, unused universe v and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U021.Proofs

/-!
# A norm class is one exactly on the norm image

The closed proposition equating the identity of the canonical norm class
with membership of its representative in the actual norm image subgroup.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- A norm class is one exactly when its representative is a local norm. -/
def NormClassEqOneIffMemStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Kˣ),
    normClass K L x = 1 ↔ x ∈ localNormSubgroup K L

end Langlands.NYLL.LocalFieldTheory
