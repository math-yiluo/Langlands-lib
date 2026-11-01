/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 1 November 2026:
Extract the statement of M093.021 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and place all six source term binders of normClass_mem_ker_iff
inside a closed Prop-valued definition, preserving their order, binder
kinds, shared universe u and membership equivalence.
Import only the published U020 Proofs module. Omit the source proof,
noncomputable section, unused universe v and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U020.Proofs

/-!
# Membership in the norm-class kernel

The closed proposition equating membership in the canonical norm-class
kernel with membership in the actual norm image subgroup.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- Membership in the kernel of the norm-class map is equivalent to membership in the local norm
subgroup. -/
def NormClassMemKerIffStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Kˣ),
    x ∈ MonoidHom.ker (normClass K L) ↔ x ∈ localNormSubgroup K L

end Langlands.NYLL.LocalFieldTheory
