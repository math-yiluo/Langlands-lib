/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 248, 3 November 2026:
Extract only the asserted type of M093.032 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and package all seven original binders inside a closed
Prop-valued definition, preserving their order, binder kinds, the shared
universe u, the extension unit z before the base unit x, and the left
multiplication by the unit norm of z.
Import only the published U031 Proofs module and preserve its entire
public chain and existing norm and quotient meanings.
Defer the truth proof; install no instance or simp registration.
Omit the original noncomputable section, unused universe v and other units.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U031.Proofs

/-!
# Left multiplication by a unit norm

The closed assertion that multiplying a base-field unit on the left by the
actual unit norm of an extension-field unit leaves its norm class unchanged.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- Multiplying a representative on the left by a unit norm leaves its norm class unchanged. -/
def NormClassNormUnitsMulStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (z : Lˣ) (x : Kˣ),
    normClass K L (normUnits K L z * x) = normClass K L x

end Langlands.NYLL.LocalFieldTheory
