# Normality of smooth algebras

Module `StacksFrontier.RingTheory.Smooth.Normal`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Normality ascends along smooth maps of commutative rings.

- `IsNormalRing.of_forall_exists_away` detects normality on basic opens. It assumes that each prime q lies in a basic open D(f) where the localized ring is normal.
- `Algebra.isNormalRing_of_smooth` gives normality of a smooth R-algebra S when R is normal.

Locally a smooth algebra is standard étale over a polynomial ring, and both steps preserve normality.

The library’s `IsNormalRing` requires each prime localization to be an integrally closed domain. This allows rings with several components.

References include Tag 033C, Tag 00H1 for polynomial rings, Tag 00GV for normality, and SGA 1 II 3.1 for ascent from the base.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [033C](https://stacks.math.columbia.edu/tag/033C) | `Algebra.isNormalRing_of_smooth` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 1 II 3.1 | `Algebra.isNormalRing_of_smooth` | normal, O_y ⇒ O_x |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Smooth/Normal.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 3 declarations of the source file 2 are kept. The 1 left out are not needed by the results for which the extract is made: `Algebra.isNormalRing_tensorProduct_of_smooth_of_isLocalization`.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
