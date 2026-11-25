# Integral characterization of universal homeomorphisms

Module `StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Universal homeomorphisms of schemes can be recognized by integrality, universal injectivity, and surjectivity.

For any scheme morphism `f`, `AlgebraicGeometry.universalHomeomorphism_iff_integral_universallyInjective_surjective` proves the equivalence with the conjunction of Mathlib’s `IsIntegralHom`, `UniversallyInjective`, and `Surjective`.

A universal homeomorphism is universally closed and universally injective. Its underlying homeomorphism makes it surjective and gives affineness by the closed-image criterion for an inducing map. Affineness and universal closedness yield integrality. Conversely, after any base change, integrality gives closedness and the other two conditions give a bijection, so the continuous map is a homeomorphism.

References are Tag 04DF, EGA IV 18.12.11 (integral case), EGA IV 2.4.5 (i), EGA IV 15.2.4 (a more general result), and SGA 4 VIII 1.4.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [04DF](https://stacks.math.columbia.edu/tag/04DF) | `universalHomeomorphism_iff_integral_universallyInjective_surjective` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 18.12.11 | `universalHomeomorphism_iff_integral_universallyInjective_surjective` | integral case |
| EGA | IV 2.4.5 | `universalHomeomorphism_iff_integral_universallyInjective_surjective` | (i) |
| EGA | IV 15.2.4 | `universalHomeomorphism_iff_integral_universallyInjective_surjective` | more general |
| SGA | 4 VIII 1.4 | `universalHomeomorphism_iff_integral_universallyInjective_surjective` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/UniversalHomeomorphism/Defs/Integral.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 4 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
