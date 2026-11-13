/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Definitions

/-!
# Coercion target for the fixed-field inclusion

Modified by Worker 290, 13 November 2026: extract the statement of M028.002
from `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/PrimeElements.lean`
at fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
`Langlands.NYLL`, use the focused inclusion import, and omit unused opens and
section variables. Replace the source theorem by a Prop-valued definition with
the `Statement` suffix, omitting its proof and simp attribute.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The source coercion identity for the fixed-field inclusion. -/
def fixedFieldInclusion_coeStatement (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a : ambientFixedAddSubgroup A K) : Prop :=
    ((fixedFieldInclusion A K L hLK a : ambientFixedAddSubgroup A L) : A.V) = a.1

end

end Langlands.NYLL.ClassFormation
