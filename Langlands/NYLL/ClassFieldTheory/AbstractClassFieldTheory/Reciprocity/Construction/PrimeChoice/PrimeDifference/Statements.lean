/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Prime.Definitions

/-!
# Target: two prime elements differ by a unit

Modified by Worker 5264, 15 November 2026: extract the statement of M030.004
from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/PrimeChoice.lean`
at fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
`Langlands.NYLL`, and replace the source module import by the published
prime-element definitions module. Replace the source theorem by a Prop-valued
definition with the `Statement` suffix, omitting its proof, and reword the
declaration docstring to describe the proposition. The target is preceded by
`set_option linter.unusedVariables false in`, which keeps the source names of
the two hypothesis binders that the proposition does not mention. See the
paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

namespace ValuationData

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

set_option linter.unusedVariables false in
/-- The proposition, from the source theorem
`sub_mem_unitAddSubgroup_of_prime`, that in additive notation two prime
elements differ by a unit: `π' - π ∈ v.unitAddSubgroup K`. -/
def sub_mem_unitAddSubgroup_of_primeStatement
    (v : ValuationData D A) (K : FiniteAbstractField G)
    {π π' : ambientFixedAddSubgroup A K.field}
    (hπ : v.IsPrimeElement K π) (hπ' : v.IsPrimeElement K π') : Prop :=
    π' - π ∈ v.unitAddSubgroup K

end ValuationData

end

end Langlands.NYLL.ClassFormation
