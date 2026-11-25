# Regularity of power series rings over a regular local ring

Module `StacksFrontier.RingTheory.RegularLocalRing.Criteria`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A power series ring in finitely many variables over a regular local ring is again a regular local ring.

`PowerSeries.isRegularLocalRing` gives `IsRegularLocalRing (PowerSeries R)` for a regular local ring R. `MvPowerSeries.isRegularLocalRing` gives the result for `MvPowerSeries (Fin n) R`, in n variables indexed by `Fin n`.

In one variable, X lies in the maximal ideal of R⟦X⟧, which therefore needs at most one generator more than its image under the constant coefficient, the maximal ideal of R; the Krull dimension grows by at least one. For a regular local R the two counts agree, so `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le` applies. The case of n variables is induction on n through `MvPowerSeries.finSuccEquiv`.

The module docstring is about regularity of a ring whose quotient by a nonzerodivisor or a regular sequence is regular local, and about a generator bound for surjections of local rings; those results are not in the file.

The table of references below gives EGA 0 17.1.4 and SGA 1 II 5.6.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 17.1.4 | `MvPowerSeries.isRegularLocalRing` | more general |
| SGA | 1 II 5.6 | `MvPowerSeries.isRegularLocalRing` | forward implication |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/RegularLocalRing/Criteria.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 5 declarations of the source file 2 are kept. The 3 left out are not needed by the results for which the extract is made: `isRegularLocalRing_of_isRegular`, `isRegularLocalRing_of_nonZeroDivisor`, `key_generator_bound`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 15 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text. The 2 on kept declarations are listed above; the 13 on declarations left out are not in the file.
