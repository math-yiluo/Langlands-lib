/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.PrimeChoice.ChosenPrime.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Prime.Definitions

/-!
# Targets: the chosen prime element is a prime element

Modified by Worker 5264, 15 November 2026: extract the statements of
M030.002, M030.003 and M030.005 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/PrimeChoice.lean`
at fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
`Langlands.NYLL`, and replace the source import by the published modules of
the chosen prime element (M030.001) and of prime elements and units. Replace
each source theorem by a Prop-valued definition with the `Statement` suffix,
omitting its proof and the `@[simp]` attribute of M030.002, and reword the
declaration docstrings to describe the propositions. The third target is
preceded by `set_option linter.unusedVariables false in`, which keeps the
source name of the hypothesis binder that the proposition does not mention.
The opens, the variable declarations and the binders are unchanged. Omit the
rest of the source file. See the paired Markdown and `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

namespace ValuationData

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

/-- The proposition, from the source theorem `valuationAt_chosenPrimeElement`,
that `v.valuationAt K (v.chosenPrimeElement K) = v.oneValue`. -/
def valuationAt_chosenPrimeElementStatement (v : ValuationData D A)
    (K : FiniteAbstractField G) : Prop :=
    v.valuationAt K (v.chosenPrimeElement K) = v.oneValue

/-- The proposition, from the source theorem `chosenPrimeElement_isPrime`,
that the chosen prime element is a prime element: its valuation is the
distinguished degree-one value. -/
def chosenPrimeElement_isPrimeStatement (v : ValuationData D A)
    (K : FiniteAbstractField G) : Prop :=
    v.IsPrimeElement K (v.chosenPrimeElement K)

set_option linter.unusedVariables false in
/-- The proposition, from the source theorem
`sub_chosenPrimeElement_mem_unitAddSubgroup`, that for a prime element `π`,
`π - v.chosenPrimeElement K ∈ v.unitAddSubgroup K`. -/
def sub_chosenPrimeElement_mem_unitAddSubgroupStatement
    (v : ValuationData D A) (K : FiniteAbstractField G)
    {π : ambientFixedAddSubgroup A K.field}
    (hπ : v.IsPrimeElement K π) : Prop :=
    π - v.chosenPrimeElement K ∈ v.unitAddSubgroup K

end ValuationData

end

end Langlands.NYLL.ClassFormation
