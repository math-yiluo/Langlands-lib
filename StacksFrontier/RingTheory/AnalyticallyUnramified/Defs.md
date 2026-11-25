# Analytically unramified local rings

Module `StacksFrontier.RingTheory.AnalyticallyUnramified.Defs`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Analytic unramifiedness is reducedness after completion at the maximal ideal of a local ring.

`StacksIsAnalyticallyUnramified R` is a proposition for a commutative local ring R with maximal ideal m. It asserts that Mathlib’s `AdicCompletion` of R at m, the inverse limit of the quotients R ⧸ mⁿ, is reduced.

The definition applies to arbitrary commutative local rings, while the Stacks definition is stated for Noetherian local rings. For a prime p of R the condition is expressed as `StacksIsAnalyticallyUnramified (R ⧸ p)`, with a local-ring instance for the quotient. The docstrings write the predicate without the prefix `Stacks`.

References are Stacks Project Tag 032X for the definition, Tag 032Y for its consequences, Tag 00MC and Tag 05GH for completion, and SGA 1 I 9.4.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [032X](https://stacks.math.columbia.edu/tag/032X) | `StacksIsAnalyticallyUnramified` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 1 I 9.4 | `StacksIsAnalyticallyUnramified` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/AnalyticallyUnramified/Defs.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 2 declarations of the source file 1 are kept. The 1 left out are not needed by the results for which the extract is made: `isAnalyticallyUnramified_iff`.
- Renamed, the source's name being declared elsewhere as well (`licenses/Stacks/STX-RENAMES.tsv.md`): `IsAnalyticallyUnramified` is `StacksIsAnalyticallyUnramified` here.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
