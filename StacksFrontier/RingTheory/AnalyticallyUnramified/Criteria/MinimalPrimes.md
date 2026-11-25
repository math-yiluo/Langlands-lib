# Analytic unramifiedness and minimal primes

Module `StacksFrontier.RingTheory.AnalyticallyUnramified.Criteria.MinimalPrimes`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a Noetherian local ring R, reducedness of the maximal-ideal completion R̂ can be tested on the quotients by minimal primes, provided R itself is reduced. Reducedness of R̂ also forces finiteness of the normalization of R.

`isAnalyticallyUnramified_iff_minimalPrimes_and_isN1` bundles two conclusions. First, R is analytically unramified exactly when R is reduced and every quotient R ⧸ q by a minimal prime q is analytically unramified. Second, if R is analytically unramified, then `StacksIsN1 R` holds: the integral closure of R in its total ring of fractions is finite as an R-module. Both conclusions are proved in `Stacks.AnalyticallyUnramified.MinimalPrimeCriterion.solution`. Private lemmas establish flat base change for annihilators of elements and finite intersections of ideals, and faithfully flat descent of N-1 between Noetherian rings.

The completion map is injective and identifies the completion of R ⧸ q with R̂ ⧸ qR̂. Each minimal prime is associated, so its extension is an annihilator and is radical if R̂ is reduced. Conversely, the extended minimal primes have zero intersection when R is reduced, so reducedness of all the quotients rules out nonzero nilpotents in R̂. The finiteness argument uses the Nagata property of R̂ to get finite integral closures on its minimal components. It embeds the integral closure of R̂ into their finite product and descends finiteness along the faithfully flat completion map.

The quantification over q has an explicit `IsLocalRing (R ⧸ q)` instance binder, supplied by properness of q. The domain case of N-1 is included in the result for arbitrary Noetherian local rings satisfying analytic unramifiedness. Analytic unramifiedness is the predicate `StacksIsAnalyticallyUnramified`, reducedness of R̂; the docstrings write it and N-1 without the prefix `Stacks`.

## References

Stacks Project Tag 032Y, Tag 032X, Tag 032F, Tag 02CE, Tag 00MB, Tag 05GH, and Tag 032W. EGA IV 7.8.3 (v) and EGA 0 7.3.3 (special case). SGA 1 IV 3.1 (special case) and SGA 3 VIIB 5.5.2 (partial).

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [032Y](https://stacks.math.columbia.edu/tag/032Y) | `isAnalyticallyUnramified_iff_minimalPrimes_and_isN1` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 7.8.3 | `isReduced_of_isReduced_adicCompletion` | (v) |
| EGA | 0 7.3.3 | `faithfullyFlat_adicCompletion` | special case |
| SGA | 1 IV 3.1 | `faithfullyFlat_adicCompletion` | special case |
| SGA | 3 VIIB 5.5.2 | `faithfullyFlat_adicCompletion` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/AnalyticallyUnramified/Criteria/MinimalPrimes.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 4 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
