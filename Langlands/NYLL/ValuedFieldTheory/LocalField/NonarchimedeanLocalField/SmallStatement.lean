/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 450 from ClassFieldTheory commit
fbd320cd8b1b06487c58227e92eb135794267709:
the theorem signature is packaged as a universal Prop-valued definition in
Langlands.NYLL, using only Mathlib interfaces. The proof is omitted.
The original license and notice are retained in licenses/NYLL/LICENSE and
licenses/NYLL/NOTICE.
-/

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Logic.Small.Basic

/-!
# Universe-zero smallness of nonarchimedean local fields: statement

The target retains an arbitrary carrier universe and the supplied valuative
relation and topology. Smallness means representability in `Type 0`, without
asserting countability.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- Every nonarchimedean local field has a carrier equivalent to a type in
`Type 0`. This definition states the universal target; it does not prove it. -/
def nonarchimedeanLocalField_smallStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K], Small.{0} K

end Langlands.NYLL.LocalFieldTheory
