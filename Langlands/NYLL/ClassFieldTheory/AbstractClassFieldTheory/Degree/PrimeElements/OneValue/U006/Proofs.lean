/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.OneValue.Statements

/-!
# Coercion of the value one

Modified by Worker 290, 16 November 2026: extract the proof of M028.006
from `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/PrimeElements.lean`
at fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
`Langlands.NYLL`, and state the theorem through its published proposition.
Keep the source proof `rfl` and complete telescope; omit the source simp
attribute because the conclusion is a named proposition. Replace the broad
source import with the focused statement module and omit unused opens.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

/-- The distinguished value one coerces to one in the ambient profinite integers. -/
theorem oneValue_coe (v : ValuationData D A) :
    oneValue_coeStatement v :=
  rfl

end ValuationData

end

end Langlands.NYLL.ClassFormation
