# The reduction as a universal homeomorphism

Module `StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Reduction`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The reduction of a scheme is the closed subscheme cut out by its nilradical ideal sheaf. Its inclusion induces a homeomorphism even after arbitrary base change.

For any scheme `X`, `AlgebraicGeometry.universalHomeomorphism_nilradical_subschemeι` registers `UniversalHomeomorphism X.nilradical.subschemeι` as an instance. The integral characterization applies because the inclusion is a closed immersion, hence integral and universally injective. Its image is the vanishing locus of the nilradical ideal sheaf, which is all of `X`, giving surjectivity.

References are Tag 054M and the universal homeomorphism assertion in EGA IV 2.4.8 (ii).

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [054M](https://stacks.math.columbia.edu/tag/054M) | `universalHomeomorphism_nilradical_subschemeι` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 2.4.8 | `universalHomeomorphism_nilradical_subschemeι` | (ii) univ. homeo |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/UniversalHomeomorphism/Reduction.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
