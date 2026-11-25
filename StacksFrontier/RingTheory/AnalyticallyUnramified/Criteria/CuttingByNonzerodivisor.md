# Analytic unramifiedness by cutting with a nonzerodivisor

Module `StacksFrontier.RingTheory.AnalyticallyUnramified.Criteria.CuttingByNonzerodivisor`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a commutative Noetherian local ring R, reducedness of its maximal-ideal-adic completion can be checked using the associated primes of the quotient by a nonzerodivisor in the maximal ideal.

`StacksIsAnalyticallyUnramified.of_associatedPrimes_quotient_span_singleton`, proved by `Stacks.AnalyticallyUnramified.CuttingCriterion.solution`, assumes a nonzerodivisor x in the maximal ideal. The hypothesis `hemb` says that every associated prime p of the R-module R/xR is minimal over xR. The hypothesis `hp` requires that R localized at each such p be regular and that R/p be analytically unramified. The conclusion is `StacksIsAnalyticallyUnramified R`, reducedness of the completion of R at its maximal ideal.

The principal ideal theorem gives height one at the associated primes, so the regular localizations are discrete valuation rings. Exactness of completion makes the quotient of the completed ring by the extended prime reduced. By the flat base change formula for associated primes, each associated prime q of the completed quotient by x is an associated prime of that reduced quotient for some such p, and Tag 032Z, applied with the discrete valuation ring R localized at p, makes the localization of the completed ring at q a discrete valuation ring, hence a domain. A square-zero element therefore vanishes in the completed quotient by x. Since x remains a nonzerodivisor after flat base change, division by x preserves the square-zero condition, and iteration puts the element in every power of the maximal ideal. Krull intersection makes it zero, which suffices for reducedness.

The nonzerodivisor hypothesis extends the local-domain case with nonzero x. Analytic unramifiedness of p is reducedness of the completion of R/p at its own maximal ideal, with locality of R/p supplied as an instance in `hp`. The second module docstring also lists as a main result the reducedness of an analytically unramified Noetherian local ring, which the file does not contain, and both docstrings write the predicate and the criterion without the prefix `Stacks`.

Tag 0330. The file cites Tag 032X and Tag 032Y for analytic unramifiedness at primes, Tag 00MB for the completed quotient, Tag 00LA and Tag 02CE for associated primes, and Tag 0312, Tag 032Z, Tag 00NP, Tag 0311, and Tag 00IP in the proof.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0330](https://stacks.math.columbia.edu/tag/0330) | `StacksIsAnalyticallyUnramified.of_associatedPrimes_quotient_span_singleton` | The source's `R` a domain with `x ≠ 0` is generalized to `x` a nonzerodivisor, \   which is all the proof uses; `R ⧸ xR` having no embedded primes is spelled as every associated \   prime of `R ⧸ xR` being minimal over `xR`, there being no predicate for it in this library. |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/AnalyticallyUnramified/Criteria/CuttingByNonzerodivisor.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 9 declarations of the source file 8 are kept. The 1 left out are not needed by the results for which the extract is made: `IsAnalyticallyUnramified.isReduced`.
- Renamed, the source's name being declared elsewhere as well (`licenses/Stacks/STX-RENAMES.tsv.md`): `IsAnalyticallyUnramified.of_associatedPrimes_quotient_span_singleton` is `StacksIsAnalyticallyUnramified.of_associatedPrimes_quotient_span_singleton` here.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
