# Birationality of the normalization morphism

Module `StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a reduced scheme, the normalization morphism identifies the generic points of
irreducible components and induces isomorphisms of their local rings.

`Scheme.isBirational_normalization` proves birationality assuming every quasi-compact
open has finitely many irreducible components. The construction starts with the
coproduct of spectra of the generic-point residue fields. For any scheme,
`Scheme.genericPointResidueSpectrum_isReduced` gives reducedness of that coproduct,
`Scheme.fromGenericPointResidueFields_injective` and
`Scheme.range_fromGenericPointResidueFields` identify its points with the generic points,
and `Scheme.surjectiveOnStalks_fromGenericPointResidueFields` gives surjectivity on
stalks. For reduced X, `Scheme.isIso_stalkMap_fromGenericPointResidueFields` makes
these stalk maps isomorphisms because the stalks of X at those points are fields.

The coproduct maps through the relative normalization, and every generic point of the
normalization lifts to the coproduct by Tag 0AXP. This gives injectivity on generic
points. For surjectivity, take the generic point of a component of the normalization
through the image of a coproduct point over the given target generic point. The stalk
comparison uses the factorization and reducedness of the normalization, which makes
its generic stalks fields as well.

The version of Tag 0BXC here uses component finiteness on quasi-compact opens, allowing
schemes with infinitely many components globally. The residue-spectrum construction
refers to Tag 035M. The stalk isomorphism is a partial result from EGA IV 20.1.3.1.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0BXC](https://stacks.math.columbia.edu/tag/0BXC) | `isBirational_normalization` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 20.1.3.1 | `isIso_stalkMap_fromGenericPointResidueFields` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/NormalizationBirational/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
