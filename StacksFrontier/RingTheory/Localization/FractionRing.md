# Total rings of fractions and minimal primes

Module `StacksFrontier.RingTheory.Localization.FractionRing`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a commutative ring R, the total ring of fractions Q(R) is `FractionRing R`, the localization at all nonzerodivisors. The file gives a product decomposition of Q(R) under a hypothesis on the zero divisors.

- `zeroDivisorsSet R` is the complement of the nonzerodivisors; by `mem_zeroDivisorsSet_iff` its elements are those that annihilate some nonzero element.
- `total_fraction_ring_isoProd_localization_atPrime` gives an R-algebra isomorphism from Q(R) to the product of the localizations R at qᵢ. It takes an injective family q indexed by `Fin t`, with each qᵢ a minimal prime, and assumes that their union equals `zeroDivisorsSet R`.

For the product, powers of elements outside one minimal prime and inside the others isolate the coordinates and give a common nonzerodivisor denominator. Prime avoidance then supplies a nonzerodivisor annihilator for differences that vanish in every factor, proving the localization property.

The product theorem takes the finite family and the equality of sets as explicit hypotheses. Its factors are local rings and can have nilpotents. The isomorphism statement uses `Nonempty` to assert existence. The module docstring also announces that Q(R) is invariant under localization at nonzerodivisors (Tag 02LW), which the file does not contain.

The Stacks Project references are Tag 02C5 for the definition and Tag 02LX for the product. The product theorem covers part of EGA II 6.4.7.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [02LX](https://stacks.math.columbia.edu/tag/02LX) | `total_fraction_ring_isoProd_localization_atPrime` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | II 6.4.7 | `total_fraction_ring_isoProd_localization_atPrime` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Localization/FractionRing.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 6 declarations of the source file 4 are kept. The 2 left out are not needed by the results for which the extract is made: `fractionRing_equiv_fractionRing_fractionRing`, `fractionRing_equiv_fractionRing_localization`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
