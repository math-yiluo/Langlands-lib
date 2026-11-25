# A fibrewise dense open of constant-dimension pieces

Module `StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibrewiseDenseRelativeDimension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A flat morphism locally of finite presentation can be restricted to a fibrewise dense open that splits into opens of constant relative dimension.

`exists_open_relativeDimension_fiberwise_dense` gives opens `U d` of the source indexed by natural numbers d. For every base point, the inverse image of their union in the scheme-theoretic fibre is dense. The restricted morphism from `U d` to the base has `RelativeDimension` d, so its nonempty fibres are equidimensional of dimension d.

`cohenMacaulayAt_of_openImmersion_source` transfers the pointwise Cohen–Macaulay condition at the image of a point to the composite along an open immersion. This lemma takes local Noetherianity of every fibre of both morphisms as explicit hypotheses. Flatness transports across the source stalk isomorphism, and the induced open immersion on fibres identifies the relevant fibre stalks.

For the decomposition, the proof restricts to the open, fibrewise dense Cohen–Macaulay locus. It uses `exists_clopen_relativeDimension` there and takes the images of those clopen pieces in the original source.

Tag 054T.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [054T](https://stacks.math.columbia.edu/tag/054T) | `exists_open_relativeDimension_fiberwise_dense` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/CohenMacaulay/FibrewiseDenseRelativeDimension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
