/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 1736, 6 November 2026 UTC:
Extract only the asserted type of M093.040 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and package all eight source binders inside a closed
Prop-valued definition. Preserve shared universe u, the named surjectivity
hypothesis h, and explicit representatives x and y after h.
Import only the published U039 Proofs module and preserve its full chain.
Defer the truth proof; install no instance or simp registration.
Disable the unused-variable linter only for this definition to retain h.
Omit the original noncomputable section, unused universe v and other units.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U039.Proofs

/-!
# Equal norm classes under a surjective unit norm

The closed assertion that surjectivity of the actual unit norm makes the
canonical norm classes of any two base-field units equal.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

set_option linter.unusedVariables false in
/-- If the unit norm is surjective, all base-field units have the same norm class. -/
def NormClassEqAllOfNormUnitsSurjectiveStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
    (h : Function.Surjective (normUnits K L)) (x y : Kˣ),
    normClass K L x = normClass K L y

end Langlands.NYLL.LocalFieldTheory
