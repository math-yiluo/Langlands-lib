# A disjoint-union criterion for normality

Module `StacksFrontier.AlgebraicGeometry.Properties.NormalCoproduct`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For locally Noetherian schemes, normality can be described by a coproduct decomposition into integral normal schemes.

`AlgebraicGeometry.isNormal_iff_exists_iso_coproduct_integral_normal` says that a locally Noetherian X is normal exactly when it is isomorphic to a coproduct of normal integral schemes.

The equivalence uses finiteness of irreducible components of the quasi-compact opens, `finite_irreducibleComponents_of_isCompact`, and the general decomposition criterion `isNormal_iff_exists_iso_coproduct`.

The index type is in the scheme’s universe and can be empty. The module docstring also announces the finite form for a Noetherian scheme; it is not in this file.

The criterion is Stacks Project Tag 033N.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [033N](https://stacks.math.columbia.edu/tag/033N) | `isNormal_iff_exists_iso_coproduct_integral_normal` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Properties/NormalCoproduct.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 2 declarations of the source file 1 are kept. The 1 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.isNormal_iff_exists_iso_finite_coproduct_integral_normal`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
