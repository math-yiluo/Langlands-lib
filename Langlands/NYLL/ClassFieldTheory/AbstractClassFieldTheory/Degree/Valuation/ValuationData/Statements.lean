/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Definitions

/-!
# Surjectivity of the value reduction and the norm-composite range targets

Modified by Worker 110, 14 November 2026: extract the statements of M025.018
and M025.020 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Valuation.lean`
at fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
`Langlands.NYLL`, import the focused valuation-data module, and omit the
unused opens and universe declaration. Replace each
source theorem by a Prop-valued definition with the `Statement` suffix,
omitting its proof, and reword each declaration docstring to describe the
proposition. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- The proposition, from the source theorem `valueModulo_surjective`, that
reduction of the value group modulo a positive integer is surjective. -/
def valueModulo_surjectiveStatement (v : ValuationData D A)
    (n : ℕ) (hn : 0 < n) : Prop :=
    Function.Surjective (v.valueModulo n hn)

/-- The proposition, from the source theorem `normCompositeAt_range`, that the
norm-valuation composite has range equal to the residue-degree multiple image. -/
def normCompositeAt_rangeStatement (v : ValuationData D A)
    (K : FiniteAbstractField G) : Prop :=
    (v.normCompositeAt K).range =
      nsmulImage v.valueGroup (K.residueDegree D : ℕ)

end ValuationData

end

end Langlands.NYLL.ClassFormation
