/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 1560, 6 November 2026 UTC:
Extract only the asserted type of M093.038 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and package all seven original binders inside a closed
Prop-valued definition. Preserve shared universe u, explicit x and y,
and the existential extension unit z with x = normUnits K L z * y.
Import only the published U037 Proofs module and preserve its full chain.
Defer the truth proof; install no instance or simp registration.
Omit the original noncomputable section, unused universe v and other units.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U037.Proofs

/-!
# Equal norm classes and left multiplication by a unit norm

The closed assertion that two base-field units have equal norm classes
exactly when a unit norm converts the second representative to the first
by multiplication on the left.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- Two norm classes agree exactly when a unit norm converts the second representative to the first
on the left. -/
def NormClassEqIffExistsNormMulLeftStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x y : Kˣ),
    normClass K L x = normClass K L y ↔
      ∃ z : Lˣ, x = normUnits K L z * y

end Langlands.NYLL.LocalFieldTheory
