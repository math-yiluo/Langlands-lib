/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Normalized.Definitions

/-!
# Targets for the divided valuation and the normalized valuation

Modified by Worker 5264, 14 November 2026: extract the statements of
M025.023, M025.024, M025.026 and M025.027 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Valuation.lean`
at fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
`Langlands.NYLL`, and import the focused normalized-valuation definitions
module. Replace each source theorem by a Prop-valued definition with the
`Statement` suffix, omitting its proof and the `@[simp]` attribute of
M025.026, and reword each declaration docstring to describe the proposition.
See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- The proposition, from the source theorem `residueDegree_nsmul_dividedAt`,
that `f_K` times the divided value is the norm composite: the identity
`f_K v_K = v ∘ N_{K|k}` before codomain restriction. -/
def residueDegree_nsmul_dividedAtStatement (v : ValuationData D A)
    (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A K.field) : Prop :=
    (K.residueDegree D : ℕ) • v.dividedAt K a = v.normCompositeAt K a

/-- The proposition, from the source theorem `dividedAt_mem_valueGroup`, that
the divided value lies in the original value group `Z`. -/
def dividedAt_mem_valueGroupStatement (v : ValuationData D A)
    (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A K.field) : Prop :=
    v.dividedAt K a ∈ v.valueGroup

/-- The proposition, from the source theorem `valuationAt_coe`, that the
underlying profinite value of the normalized valuation is the divided
valuation. -/
def valuationAt_coeStatement (v : ValuationData D A) (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A K.field) : Prop :=
    (v.valuationAt K a : ZHat) = v.dividedAt K a

/-- The proposition, from the source theorem `normalizedValuation_surjective`
(normalized-valuation functoriality, surjectivity), that the normalized
valuation over a finite abstract field maps onto `Z`. -/
def normalizedValuation_surjectiveStatement (v : ValuationData D A)
    (K : FiniteAbstractField G) : Prop :=
    Function.Surjective (v.valuationAt K)

end ValuationData

end

end Langlands.NYLL.ClassFormation
