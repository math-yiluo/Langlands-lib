# Normal rings and directed colimits

Module `StacksFrontier.RingTheory.IntegrallyClosed.Defs`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file defines normality through prime localizations. It proves that normal rings are integrally closed in their total rings of fractions, and that normality is preserved by localization and directed colimits.

## Definitions and results

- `IsNormalRing` is the predicate that every localization of a commutative ring at a prime is an integrally closed domain. The file gives transport across ring isomorphisms (`IsNormalRing.congr`), shows that a normal local ring is an integrally closed domain (`IsNormalRing.of_isLocalRing`), and that an integrally closed domain is normal (`IsNormalRing.of_isIntegrallyClosed`).
- `IsNormalRing.isLocalization` proves normality for any localization of a normal ring.
- `IsIntegrallyClosed.of_forall_localization_maximal` proves that a commutative ring is integrally closed in its total ring of fractions if all its maximal localizations are integrally closed. `IsNormalRing.isIntegrallyClosed` applies this to normal rings.
- `Ring.DirectLimit.isDomain` and `Ring.DirectLimit.isIntegrallyClosed` prove the corresponding results for a directed system of domains and of integrally closed domains, respectively. `directLimit_isNormalRing` proves normality of the colimit of a system of normal rings. These systems are indexed by a nonempty directed preorder.

The local-to-global proof clears a denominator outside each maximal ideal, then uses the local test for membership in the image of the ring. For integral closedness of a colimit of domains, the numerator, denominator, and coefficients of a monic equation come from one stage and the cleared equation holds at a later stage. The general normality result uses `Ring.DirectLimit.isLocalization` to express each prime localization of the colimit as a colimit of the corresponding prime localizations.

## Scope and references

Normality is local and allows rings with zero divisors. The maximal-localization criterion uses the total ring of fractions for arbitrary commutative rings. The directed colimit results allow arbitrary ring homomorphisms satisfying the directed-system laws.

The normal-ring definition, localization, integral closedness, and colimit results are Tag 00GV, Tag 037C, Tag 034M, and Tag 037D. The table of tags below also records Tag 0309 and the two Mathlib localization facts corresponding to Tag 00GY. References for normality and colimits include EGA IV 5.13.3, EGA IV 5.13.4, EGA IV 5.13.5, and EGA IV 5.13.6, with EGA IV 6.14.1.1 for the implication from normality to integral closedness.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00GV](https://stacks.math.columbia.edu/tag/00GV) | `IsNormalRing` |  |
| [037C](https://stacks.math.columbia.edu/tag/037C) | `IsNormalRing.isLocalization` |  |
| [034M](https://stacks.math.columbia.edu/tag/034M) | `IsNormalRing.isIntegrallyClosed` |  |
| [037D](https://stacks.math.columbia.edu/tag/037D) | `directLimit_isNormalRing` |  |
| [0309](https://stacks.math.columbia.edu/tag/0309) | `IsIntegrallyClosed` |  |
| [0309](https://stacks.math.columbia.edu/tag/0309) | `isIntegrallyClosed_iff` | identified with the Stacks wording |
| [00GY](https://stacks.math.columbia.edu/tag/00GY) | `IsLocalization.isDomain_of_le_nonZeroDivisors` | the localization is a domain |
| [00GY](https://stacks.math.columbia.edu/tag/00GY) | `isIntegrallyClosed_of_isLocalization` | the localization is integrally closed |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 5.13.5 | `IsNormalRing` |  |
| EGA | IV 5.13.6 | `IsNormalRing` |  |
| EGA | IV 6.14.1.1 | `IsNormalRing.isIntegrallyClosed` | (i) necessity |
| EGA | IV 5.13.3 | `Ring.DirectLimit.isDomain` |  |
| EGA | IV 5.13.4 | `Ring.DirectLimit.isIntegrallyClosed` | more general |
| EGA | IV 5.13.1 | `Ring.DirectLimit.comap_of_eq_comap_comap_of` | Clause (ii) |
| EGA | IV 5.13.6 | `directLimit_isNormalRing` | more general |
| EGA | IV 14.5.5 | `IsIntegrallyClosed` |  |
| EGA | IV 7.5.3 | `IsIntegrallyClosed` | (vi), partial |
| EGA | II 8.11.8 | `isIntegrallyClosed_of_isLocalization` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/IntegrallyClosed/Defs.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 28 declarations of the source file 23 are kept. The 5 left out are not needed by the results for which the extract is made: `IsNormalDomain`, `IsNormalDomain.isDomain`, `IsNormalDomain.isIntegrallyClosed`, `IsNormalDomain.mk`, `IsNormalRing.isReduced`.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 10 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
