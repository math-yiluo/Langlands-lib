/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.OneValue.Definitions

/-!
# Coercion target for the value one

Modified by Worker 110, 14 November 2026: extract the statement of M028.006
from `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/PrimeElements.lean`
at fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
`Langlands.NYLL`, use the focused one-value import, and omit unused opens.
Replace the source theorem by a Prop-valued definition with the `Statement`
suffix, omitting its proof and simp attribute, and reword its docstring to
describe the proposition.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

/-- The proposition, from the source theorem `oneValue_coe`, that the value
one coerces to `(1 : ZHat)`: `(v.oneValue : ZHat) = 1`. -/
def oneValue_coeStatement (v : ValuationData D A) : Prop :=
    (v.oneValue : ZHat) = 1

end ValuationData

end

end Langlands.NYLL.ClassFormation
