/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# NYLL M020: pulled-back cyclic factor subgroups

Modified by Worker 4918: extract M020.002 `cyclicFactorSubgroup` and M020.003
`cyclicFactorSubgroup_normal` from the pinned NYLL
`Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianCyclicFactors.lean`,
prefix the namespace with `Langlands.NYLL`, keep only the source's Mathlib
import, and drop `open CyclicCohomology`, which these two declarations do not
use. The declarations, their binders and their bodies are otherwise unchanged.
The paired Markdown records every modification. See `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE`.

Given a normal subgroup `H` of `P` and a homomorphism `f : P ⧸ H →* C`, the
pulled-back factor kernel is the kernel of `P → P ⧸ H → C`.
-/

namespace Langlands.NYLL.KummerTheory

noncomputable section

section FiniteAbelianCyclicFactors

section Pullback

variable {P C : Type*} [Group P] [Group C]
  (H : Subgroup P) [H.Normal]

/-- Pull a quotient-factor kernel back to the original group. -/
def cyclicFactorSubgroup (f : (P ⧸ H) →* C) : Subgroup P :=
  MonoidHom.ker (f.comp (QuotientGroup.mk' H))

/-- The kernel subgroup attached to a cyclic quotient factor is normal. -/
instance cyclicFactorSubgroup_normal (f : (P ⧸ H) →* C) :
    (cyclicFactorSubgroup H f).Normal :=
  MonoidHom.normal_ker _

end Pullback

end FiniteAbelianCyclicFactors

end

end Langlands.NYLL.KummerTheory
