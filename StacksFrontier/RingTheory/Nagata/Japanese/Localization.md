# Localization of Nagata rings

Module `StacksFrontier.RingTheory.Nagata.Japanese.Localization`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file proves that a localization of a Nagata ring is Nagata, using preservation of the Japanese condition for localizations of domains.

`isNagata_of_isLocalization` assumes that the commutative ring `R` is Nagata and that an `R`-algebra `T` realizes localization at a submonoid `M`. It concludes `StacksIsNagataRing T`. The domain lemma `isN2_of_isLocalization_domain` passes `IsN2_032u` from a domain `D` to a domain localization of `D` at nonzerodivisors. The related helper `isFractionRing_of_field_isLocalization` identifies an injective localization of a domain into a field as a fraction field of that domain.

Noetherianity localizes. For a prime of `T`, the quotient is a localization of the quotient of `R` by its contraction, at the image of `M`. The domain lemma uses the common fraction field and `IsLocalization.integralClosure` to transfer module finiteness of the integral closure to the localized base.

The main theorem allows an arbitrary multiplicative submonoid of a general commutative ring. The nonzerodivisor condition is needed in the domain lemma and is established on the prime quotients. The base and localization share a universe, as do the extension fields used for N-2.

References are Tag 032U for the Nagata theorem, Tag 032G for the Japanese localization step, Tag 0307 for localization of integral closure, and EGA IV 7.7.2.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [032U](https://stacks.math.columbia.edu/tag/032U) | `isNagata_of_isLocalization` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 7.7.2 | `isNagata_of_isLocalization` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Nagata/Japanese/Localization.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 4 declarations of the source file 3 are kept. The 1 left out are not needed by the results for which the extract is made: `isN1_of_isN2`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
