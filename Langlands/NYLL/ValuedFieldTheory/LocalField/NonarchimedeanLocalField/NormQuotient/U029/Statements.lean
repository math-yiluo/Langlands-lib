/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 1 November 2026:
Extract only the asserted type of M093.029 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and package all seven original binders inside a closed
Prop-valued definition, preserving the shared universe u, implicit x
and explicit hx. Import only the published U028 Proofs module and
preserve its entire public chain and existing norm and quotient meanings.
Defer the truth proof; install no instance or simp registration.
Disable the unused-variable linter only for this definition to retain hx.
Omit the original noncomputable section, unused universe v and other units.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U028.Proofs

/-!
# Norm-image membership gives trivial norm class

The closed assertion that a representative in the actual unit-norm image
maps to the identity under the canonical norm-quotient projection.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

set_option linter.unusedVariables false in
/-- A representative from the local norm subgroup has trivial norm class. -/
def NormClassEqOneOfMemStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
    {x : Kˣ} (hx : x ∈ localNormSubgroup K L), normClass K L x = 1

end Langlands.NYLL.LocalFieldTheory
