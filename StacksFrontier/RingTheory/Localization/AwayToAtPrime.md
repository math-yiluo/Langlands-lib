# Embedding a principal localization into a prime localization

Module `StacksFrontier.RingTheory.Localization.AwayToAtPrime`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a prime ideal p and an element f outside p, `localizationAwayToAtPrime` constructs the canonical map R_f → R_p, over any commutative semiring.

Over a commutative ring, `localizationAwayToAtPrime_injective_iff` says the map is injective exactly when every a ∈ R that vanishes in R_p is killed by some power of f.

`exists_injective_localizationAwayToAtPrime_of_isReduced_finite_minimalPrimes` assumes R is reduced and that the minimal primes q with q ⊈ p are finite in number, and produces an f outside p with injective map: f lies in all those primes but not in p. If a vanishes in R_p, some element outside p kills a, so fa lies in every minimal prime and reducedness gives fa = 0.

Part (3) of Tag 0BX1 assumes finiteness of all minimal primes. The module docstring also lists the domain and Noetherian cases of that tag, which are not in the file. The construction of the map is cited as a special case of EGA 0 1.5.1.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0BX1](https://stacks.math.columbia.edu/tag/0BX1) | `exists_injective_localizationAwayToAtPrime_of_isReduced_finite_minimalPrimes` | (3) |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 1.5.1 | `localizationAwayToAtPrime` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Localization/AwayToAtPrime.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 7 declarations of the source file 4 are kept. The 3 left out are not needed by the results for which the extract is made: `exists_injective_localizationAwayToAtPrime_of_isDomain`, `exists_injective_localizationAwayToAtPrime_of_isNoetherianRing`, `injective_localizationAwayToAtPrime_of_ann`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
