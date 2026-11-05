/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 1560, 5 November 2026 UTC:
Extract only the asserted type of M093.036 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and package all nine original binders inside a closed
Prop-valued definition. Preserve shared universe u, implicit x and y,
explicit z and the named hypothesis h with the unit norm on the left.
Import only the published U035 Proofs module and preserve its full chain.
Defer the truth proof; install no instance or simp registration.
Disable the unused-variable linter only for this definition to retain h.
Omit the original noncomputable section, unused universe v and other units.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U035.Proofs

/-!
# Equal norm classes from left multiplication by a unit norm

The closed assertion that two base-field units have the same norm class
when the first equals an extension-unit norm times the second.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

set_option linter.unusedVariables false in
/-- A representative obtained by multiplying another by a unit norm defines the same norm class. -/
def NormClassEqOfEqNormUnitsMulStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] {x y : Kˣ} (z : Lˣ)
    (h : x = normUnits K L z * y), normClass K L x = normClass K L y

end Langlands.NYLL.LocalFieldTheory
