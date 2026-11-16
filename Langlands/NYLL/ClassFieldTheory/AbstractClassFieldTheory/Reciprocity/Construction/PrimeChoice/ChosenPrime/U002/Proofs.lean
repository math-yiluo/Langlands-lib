/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.PrimeChoice.ChosenPrime.Statements

/-!
# NYLL M030.002: the chosen prime element has valuation one

Modified by Worker 5264, 15 November 2026: prove the target
`ValuationData.valuationAt_chosenPrimeElementStatement` (M030.002) by the
source proof of `ValuationData.valuationAt_chosenPrimeElement` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/PrimeChoice.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the target proposition as its type and
begin the proof with `show` stating it unfolded. The source term
`Classical.choose_spec (v.normalizedValuation_surjective K v.oneValue)` names
the theorem M025.027, whose proof is not published (the published
`chosenPrimeElement` uses its source proof in place); the port applies
`Classical.choose_spec` with the predicate given explicitly and lets
unification find the existence proof inside `chosenPrimeElement`. Omit the
source `@[simp]` attribute (the conclusion is the target proposition, not an
equation), replace the source imports by the target's statement module and
omit the rest of the source file. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

namespace ValuationData

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

/-- Establishes the identity `v.valuationAt K (v.chosenPrimeElement K) = v.oneValue`. -/
theorem valuationAt_chosenPrimeElement (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    valuationAt_chosenPrimeElementStatement v K := by
  show v.valuationAt K (v.chosenPrimeElement K) = v.oneValue
  exact Classical.choose_spec (p := fun a => v.valuationAt K a = v.oneValue) _

end ValuationData

end

end Langlands.NYLL.ClassFormation
