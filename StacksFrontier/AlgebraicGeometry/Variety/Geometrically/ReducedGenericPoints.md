# Geometric reducedness at generic points

Module `StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedGenericPoints`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

On a scheme over a field, geometric reducedness at a point with reduced local ring, and geometric reducedness of a reduced scheme, can be tested at the generic points of irreducible components.

- `AlgebraicGeometry.isGeometricallyReducedAt_of_isReduced_stalk_of_genericPoints` gives geometric reducedness at x if its local ring is reduced and the scheme is geometrically reduced at every generic point of an irreducible component that specializes to x.
- `geometricallyReduced_of_isGeometricallyReducedAt_genericPoints` gives geometric reducedness (Mathlib's `GeometricallyReduced f`) of a reduced scheme over the field from the condition at the generic points of all its irreducible components.

The proofs use the equivalence between geometric reducedness at a point and geometric reducedness of its local ring. A reduced ring is geometrically reduced when its localizations at minimal primes are; the minimal primes of the local ring at x correspond to the generic points specializing to x, and the localization at such a prime is the local ring at that generic point.

The implications require reducedness at the point or on the whole scheme as stated. The module docstring also announces that geometric reducedness passes to generalizations and a function-field criterion for integral schemes; neither is in the file.

The results are attributed to Tag 04KS.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [04KS](https://stacks.math.columbia.edu/tag/04KS) | `isGeometricallyReducedAt_of_isReduced_stalk_of_genericPoints` | geometric_reducedness_at_point_of_generic_points |
| [04KS](https://stacks.math.columbia.edu/tag/04KS) | `geometricallyReduced_of_isGeometricallyReducedAt_genericPoints` | geometric_reducedness_of_generic_points |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Variety/Geometrically/ReducedGenericPoints.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 11 declarations of the source file 8 are kept. The 3 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.geometricallyReduced_iff_isSeparableExtension_functionField`, `AlgebraicGeometry.isGeometricallyReducedAt_of_specializes`, `AlgebraicGeometry.isSeparableExtension_congr`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
