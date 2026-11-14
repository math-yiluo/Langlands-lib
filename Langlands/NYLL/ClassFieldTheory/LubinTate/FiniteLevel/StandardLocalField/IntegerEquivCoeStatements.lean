/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 411, 2026-11-14: extract only the statements of
M335.006 (lines 91–98) and M335.007 (lines 100–107) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL, add the `Statement` suffix, state each theorem as a
Prop-valued definition without its proof or `simp` attribute, and import
only the M335.005 module. See the paired Markdown.
License and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.IntegerEquiv

/-!
# Coercion targets for the standard integer-ring equivalence

Prop-valued targets stating that `standardLocalFieldIntegerEquiv K` and its
inverse preserve the underlying element of `K`.
-/

open scoped ValuativeRel

namespace Langlands.NYLL.LubinTate

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The canonical integer-ring equivalence preserves the underlying field
element. -/
def standardLocalFieldIntegerEquiv_apply_coeStatement (x : 𝒪[K]) : Prop :=
  (((standardLocalFieldIntegerEquiv K x :
      (standardLocalField K).valuationSubring)) : K) =
    (x : K)

/-- The inverse canonical integer-ring equivalence preserves the underlying
field element. -/
def standardLocalFieldIntegerEquiv_symm_apply_coeStatement
    (x : (standardLocalField K).valuationSubring) : Prop :=
  ((((standardLocalFieldIntegerEquiv K).symm x : 𝒪[K])) : K) =
    (x : K)

end Langlands.NYLL.LubinTate
