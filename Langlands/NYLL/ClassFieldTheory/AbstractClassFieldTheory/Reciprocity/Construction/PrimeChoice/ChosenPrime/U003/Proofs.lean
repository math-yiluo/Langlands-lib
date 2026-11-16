/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.PrimeChoice.ChosenPrime.Statements

/-!
# NYLL M030.003: the chosen prime element is a prime element

Modified by Worker 5264, 15 November 2026: prove the target
`ValuationData.chosenPrimeElement_isPrimeStatement` (M030.003) by the source
proof of `ValuationData.chosenPrimeElement_isPrime` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/PrimeChoice.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the target proposition as its type and
begin the proof with `show` stating it unfolded. The source term
`v.valuationAt_chosenPrimeElement K` names the theorem M030.002, whose proof
is not yet in the Library; this module proves that equation as the private
theorem `valuationAt_chosenPrimeElement_aux`, by `Classical.choose_spec`
with the predicate given explicitly (the source proof of M030.002 names
M025.027, whose proof is not yet in the Library and whose source proof the
published `chosenPrimeElement` uses in place). Replace the source imports by the target's statement module
and omit the rest of the source file. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

Modified by Worker 743, 16 November 2026: status wording in this comment
only ("not yet in the Library").
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

namespace ValuationData

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

/-- The identity `v.valuationAt K (v.chosenPrimeElement K) = v.oneValue`
(the source theorem `valuationAt_chosenPrimeElement`, M030.002). -/
private theorem valuationAt_chosenPrimeElement_aux (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    v.valuationAt K (v.chosenPrimeElement K) = v.oneValue :=
  Classical.choose_spec (p := fun a => v.valuationAt K a = v.oneValue) _

/-- The chosen prime element has valuation equal to the distinguished degree-one value. -/
theorem chosenPrimeElement_isPrime (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    chosenPrimeElement_isPrimeStatement v K := by
  show v.IsPrimeElement K (v.chosenPrimeElement K)
  exact valuationAt_chosenPrimeElement_aux v K

end ValuationData

end

end Langlands.NYLL.ClassFormation
