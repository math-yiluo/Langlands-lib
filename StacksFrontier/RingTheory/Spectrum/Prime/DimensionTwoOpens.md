# Infinite opens in spectra of local domains

Module `StacksFrontier.RingTheory.Spectrum.Prime.DimensionTwoOpens`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Every nonempty open in the spectrum of a Noetherian local domain of Krull dimension at least two has infinitely many points.

`PrimeSpectrum.infinite_of_two_le_ringKrullDim`, proved by `Stacks.Spectrum.InfiniteOpens.solution`, takes a commutative Noetherian local domain R with `2 ≤ ringKrullDim R` and an open nonempty set U in `PrimeSpectrum R`, and proves `U.Infinite`.

A private lemma uses finite prime avoidance to produce infinitely many height-one primes whenever a Noetherian domain has a prime of height at least two. In a nonempty basic open D(x) inside U, the excluded height-one primes are the minimal primes over the nonzero principal ideal (x), a finite set by Noetherianity and Krull’s principal ideal theorem.

Locality supplies the prime of height at least two, since the maximal ideal has height equal to the dimension.

References include Tag 02IG, EGA IV 5.2.5 and EGA IV 10.5.1.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [02IG](https://stacks.math.columbia.edu/tag/02IG) | `infinite_of_two_le_ringKrullDim` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 5.2.5 | `mem_minimalPrimes_span_singleton_iff_height_eq_one` | more general |
| EGA | IV 10.5.1 | `infinite_setOf_height_eq_one` | e) |
| EGA | IV 10.5.1 | `infinite_of_two_le_ringKrullDim` | e) ⇒ f) for local B |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Spectrum/Prime/DimensionTwoOpens.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 3 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
