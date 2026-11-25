# Heights along saturated chains of prime ideals

Module `StacksFrontier.RingTheory.RegularRing.Dimension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

In a regular ring, a saturated chain from 𝔭 to 𝔮 has length equal to the difference of their heights. Saturation means that each step is a covering pair of prime ideals.

`IsRegularRing.height_last_eq_length_add_height_head`, also proved as `Stacks.RegularRing.MaximalChains.solution`, takes a finite `RelSeries` for the covering relation on `PrimeSpectrum R`, with R a commutative regular ring. It gives the additive formula height(𝔮) = length + height(𝔭), counting steps in the chain.

The private lemma `height_eq_height_add_one_of_covBy_of_isMaximalCohenMacaulay` gives a height increment of one across a covering pair 𝔭 ⋖ 𝔮 whenever a Noetherian local model A of R localized at 𝔮 is maximal Cohen–Macaulay over itself.

The Cohen–Macaulay dimension formula gives the increment because 𝔭A has coheight one by the prime correspondence, making A/𝔭A one-dimensional. Regularity supplies Cohen–Macaulayness at each step, and induction adds the increments.

The statement applies to arbitrary regular rings, extending the tagged case of a polynomial ring in finitely many variables over a field. Both heights are computed in R at the endpoints of the given chain.

Stacks Project Tag 00OR for the chain formula, Tag 00NQ for Cohen–Macaulayness of regular local rings, and Tag 00NA for the dimension formula.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00OR](https://stacks.math.columbia.edu/tag/00OR) | `IsRegularRing.height_last_eq_length_add_height_head` | Stated for an arbitrary regular ring, of which a polynomial algebra in finitely many variables over a field is an instance (the source's ring, via Proposition 00OQ); a maximal chain between `𝔭` and `𝔮` is a `RelSeries` for the covering relation `⋖` on `PrimeSpectrum R` with the given head and last, and the formula is stated additively. See the module docstring. |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/RegularRing/Dimension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
