# Associated primes, support, and localization

Module `StacksFrontier.RingTheory.Ideal.AssociatedPrime.Support`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file relates the minimal points of the support of a module to its associated primes. It also shows that localization at the associated primes detects whether a module element is zero.

## Main results

- `Module.setOf_minimal_support_eq_setOf_minimal_associatedPrimes` identifies the minimal points of the support of a finitely generated module over a Noetherian commutative ring with its minimal associated primes. It compares two sets of points of the prime spectrum, using `PrimeSpectrum.asIdeal` to interpret associated primes as points.
- `Module.mem_associatedPrimes_of_minimal_mem_support` shows that any prime minimal in the support of an arbitrary module over a Noetherian commutative ring is associated to the module.
- `assMap` sends an element m of an R-module to the tuple of fractions m/1 in the localizations at its associated primes. `zero_at_ass_zero` proves this map injective over a Noetherian commutative ring, with no finite generation hypothesis on the module.

For finite modules, the support is the zero locus of the annihilator, so its minimal points correspond to minimal primes over that ideal. The general minimal-support result uses that the support is the union of the supports of cyclic submodules. For injectivity, if m vanishes at each associated prime, the proof rules out any associated prime of Rm, forcing Rm to be zero.

## Scope and references

The equality of minimal sets is the comparison of parts (1) and (2) of Tag 02CE. The identification with minimal primes over the annihilator uses the support description cited as Tag 00L7. The injectivity and minimal-support results are Tag 0311 and Tag 05BV, respectively.

The file points to the imported formulas `biUnion_associatedPrimes_eq_zero_divisors` and `biUnion_associatedPrimes_eq_compl_regular` for the union of associated primes as the zerodivisor set over a Noetherian ring. The tables below attribute them to Tag 00LD and EGA IV 20.2.13.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [02CE](https://stacks.math.columbia.edu/tag/02CE) | `setOf_minimal_support_eq_setOf_minimal_associatedPrimes` | Parts (1) and (2); the equality with part (3) is the first conclusion of \   Stacks 00L7, which the source's own proof cites for that step. |
| [0311](https://stacks.math.columbia.edu/tag/0311) | `zero_at_ass_zero` |  |
| [05BV](https://stacks.math.columbia.edu/tag/05BV) | `Module.mem_associatedPrimes_of_minimal_mem_support` |  |
| [00LD](https://stacks.math.columbia.edu/tag/00LD) | `biUnion_associatedPrimes_eq_zero_divisors` |  |
| [00LD](https://stacks.math.columbia.edu/tag/00LD) | `biUnion_associatedPrimes_eq_compl_regular` | the same union, phrased via `IsSMulRegular` |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 20.2.13 | `biUnion_associatedPrimes_eq_zero_divisors` | S |
| EGA | IV 20.2.13 | `biUnion_associatedPrimes_eq_compl_regular` | S |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Ideal/AssociatedPrime/Support.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
