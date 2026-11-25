# Continuous and adic square-zero lifting

Module `StacksFrontier.RingTheory.FormallySmooth.Topological`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file defines two square-zero lifting predicates for ring maps and proves that the first is stable under composition.

`RingHom.FormallySmoothTop` for φ : R → S requires that, given a discrete ring A, a square-zero ideal J, and compatible continuous maps R → A and S → A/J, there be a continuous map S → A extending the first and lifting the second. `RingHom.FormallySmoothTop.comp` composes two such lifting properties when the second arrow is continuous.

`RingHom.FormallySmoothNAdic` is the algebraic lifting predicate relative to an ideal n of S. It asks for compatible ring maps R → A and S → A/J with J² = 0 to have a commuting lift when S → A/J kills nᵏ for some k ≥ 1.

The composition proof lifts along the first arrow and uses that lift as the base map for lifting along the second.

Continuity of an original arrow is a separate hypothesis when required. `RingHom.FormallySmoothTop` allows arbitrary topological ring structures on R and S. The universe of the test ring is independent of their universes in both predicates. The module docstring also lists a monotonicity result in the ideal (Tag 07EE), and the file ends with an empty section of that title; that result is not in this file.

## References

Stacks Project, Tag 07E8 and Tag 07EB for the topological setting, Tag 07EF for composition, and Tag 07NI, Tag 07EC and Tag 07EE for the adic predicate.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [07EF](https://stacks.math.columbia.edu/tag/07EF) | `FormallySmoothTop.comp` |  |
| [07NI](https://stacks.math.columbia.edu/tag/07NI) | `FormallySmoothNAdic` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/FormallySmooth/Topological.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 4 declarations of the source file 3 are kept. The 1 left out are not needed by the results for which the extract is made: `RingHom.FormallySmoothNAdic.mono`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- The one reference to EGA or SGA that the source writes as an attribute of that library belongs to the declaration left out; it is not in this file.
