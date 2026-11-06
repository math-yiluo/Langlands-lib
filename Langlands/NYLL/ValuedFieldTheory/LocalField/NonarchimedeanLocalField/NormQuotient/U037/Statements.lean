/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 1560, 5 November 2026 UTC:
Extract only the asserted type of M093.037 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and package all seven original binders inside a closed
Prop-valued definition. Preserve shared universe u, explicit x and y,
and the product x * y⁻¹ with x on the left.
Import only the published U036 Proofs module and preserve its full chain.
Defer the truth proof; install no instance or simp registration.
Omit the original noncomputable section, unused universe v and other units.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U036.Proofs

/-!
# Equality of norm classes and multiplication by an inverse

The closed assertion that two base-field units have equal norm classes
exactly when the first times the inverse of the second is a local norm.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- Two norm classes agree exactly when one representative times the other's inverse is a local
norm. -/
def NormClassEqIffMulInvMemStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x y : Kˣ),
    normClass K L x = normClass K L y ↔ x * y⁻¹ ∈ localNormSubgroup K L

end Langlands.NYLL.LocalFieldTheory
