/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.PrimeChoice.ChosenPrime.Statements

/-!
# NYLL M030.005: a prime element differs from the chosen one by a unit

Modified by Worker 5264, 15 November 2026: prove the target
`ValuationData.sub_chosenPrimeElement_mem_unitAddSubgroupStatement`
(M030.005) by the source proof of
`ValuationData.sub_chosenPrimeElement_mem_unitAddSubgroup` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/PrimeChoice.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the target proposition as its type and
begin the proof with `show` stating it unfolded. The source term applies
`sub_mem_unitAddSubgroup_of_prime` (M030.004) and
`chosenPrimeElement_isPrime` (M030.003), whose proofs are not yet in
the Library; this module proves them as the private theorems
`sub_mem_unitAddSubgroup_of_prime_aux` (by its source proof, rewriting with
a local copy `hmem` of the `Iff.rfl` lemma `mem_unitAddSubgroup_iff`,
M028.009, whose proof is not yet in the Library) and `chosenPrimeElement_isPrime_aux`
(by `Classical.choose_spec` with the predicate given explicitly, which
proves M030.002 and hence M030.003). Replace the source imports by the
target's statement module and omit the rest of the source file. See the
paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

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

/-- The chosen prime element has valuation equal to the distinguished
degree-one value (the source theorems `valuationAt_chosenPrimeElement`,
M030.002, and `chosenPrimeElement_isPrime`, M030.003). -/
private theorem chosenPrimeElement_isPrime_aux (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    v.IsPrimeElement K (v.chosenPrimeElement K) :=
  Classical.choose_spec (p := fun a => v.valuationAt K a = v.oneValue) _

/-- In additive notation, two prime elements differ by a unit (the source
theorem `sub_mem_unitAddSubgroup_of_prime`, M030.004, proved by its source
proof). -/
private theorem sub_mem_unitAddSubgroup_of_prime_aux
    (v : ValuationData D A) (K : FiniteAbstractField G)
    {π π' : ambientFixedAddSubgroup A K.field}
    (hπ : v.IsPrimeElement K π) (hπ' : v.IsPrimeElement K π') :
    π' - π ∈ v.unitAddSubgroup K := by
  have hmem : ∀ u : ambientFixedAddSubgroup A K.field,
      u ∈ v.unitAddSubgroup K ↔ v.valuationAt K u = 0 :=
    fun _ => Iff.rfl
  rw [hmem, map_sub, hπ, hπ']
  exact sub_self _

/-- Establishes the membership statement `π - v.chosenPrimeElement K ∈ v.unitAddSubgroup K`. -/
theorem sub_chosenPrimeElement_mem_unitAddSubgroup
    (v : ValuationData D A) (K : FiniteAbstractField G)
    {π : ambientFixedAddSubgroup A K.field}
    (hπ : v.IsPrimeElement K π) :
    sub_chosenPrimeElement_mem_unitAddSubgroupStatement v K hπ := by
  show π - v.chosenPrimeElement K ∈ v.unitAddSubgroup K
  exact sub_mem_unitAddSubgroup_of_prime_aux v
    K (chosenPrimeElement_isPrime_aux v K) hπ

end ValuationData

end

end Langlands.NYLL.ClassFormation
