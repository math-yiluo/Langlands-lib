# Associated and weakly associated primes over a Noetherian ring

Module `StacksFrontier.RingTheory.Ideal.AssociatedPrime.WeaklyAssociated`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A prime p of a commutative semiring R is weakly associated to an R-module M if it is minimal among the primes containing the annihilator of some element of M. The file proves that over a Noetherian ring these are exactly the associated primes in Mathlib's sense.

## Main results

- `associatedPrimes_eq_setOf_exists_mem_minimalPrimes_annihilator`: for a Noetherian commutative semiring R and an R-module M that is only an additive commutative monoid, `associatedPrimes R M` is the set of ideals p with p ∈ `(R ∙ m).annihilator.minimalPrimes` for some m in M.

One inclusion is formal: Mathlib's `IsAssociatedPrime` asks that p be prime and equal to the radical of an element annihilator, and such a p is minimal over that annihilator. The other is Mathlib's `Submodule.exists_eq_colon_of_mem_minimalPrimes`, applied after identifying `(R ∙ m).annihilator` with the colon ideal of `⊥` by `{m}`.

## Scope and references

Weak association is written explicitly using `Ideal.minimalPrimes` of the annihilator of a cyclic submodule; it has no name of its own. The result is Tag 058A in the Noetherian case. The module docstrings of the file also describe a comparison for finitely generated primes, a result on the support and two inclusions for exact sequences, none of which the file contains.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [058A](https://stacks.math.columbia.edu/tag/058A) | `associatedPrimes_eq_setOf_exists_mem_minimalPrimes_annihilator` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Ideal/AssociatedPrime/WeaklyAssociated.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 22 declarations of the source file 1 are kept. The 21 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
