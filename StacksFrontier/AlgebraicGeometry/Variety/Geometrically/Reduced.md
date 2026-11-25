# Geometric reducedness at a point

Module `StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a scheme over a field, geometric reducedness at a point can be read from its local ring.

`AlgebraicGeometry.IsGeometricallyReducedAt f x` asks that every point above x after every field extension have a reduced local ring. The theorem `geometricallyReduced_iff_forall_isGeometricallyReducedAt` identifies Mathlib's `GeometricallyReduced f`, for a structure morphism to Spec k, with this condition at every point.

- `isGeometricallyReducedAt_iff_isGeometricallyReduced_stalk` equates the pointwise condition with geometric reducedness of the local ring as a k-algebra.
- `isReduced_tensorProduct_of_forall_isReduced_stalk` gives a comparison for a purely inseparable extension K/k. If the stalks above x after base change are reduced, then so is the tensor product of K with the local ring at x.

The stalk after base change is a localization of the tensor product with the original stalk. For purely inseparable extensions, powers of elements of the tensor product come from the original stalk, so the elements inverted are already units. This gives the converse comparison needed for the algebraic test by finite purely inseparable extensions.

The predicate defined here concerns schemes over fields. Mathlib's morphism predicate allows arbitrary bases. The field extensions and scheme in the pointwise test share a Lean universe. The k-algebra structure on the stalk is induced by the stalk map of f.

The pointwise definition is the condition of part (1) of Tag 035V, and the stalk criterion is Tag 035W. The pointwise definition refers to EGA IV 4.6.12. The module docstring and the docstrings of the first two declarations also speak of a predicate for geometric reducedness over the field, at every point, which carries Tag 035V, and the module docstring announces results over a perfect field; none of these is in the file.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [035W](https://stacks.math.columbia.edu/tag/035W) | `isGeometricallyReducedAt_iff_isGeometricallyReduced_stalk` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 4.6.12 | `IsGeometricallyReducedAt` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Variety/Geometrically/Reduced.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 9 declarations of the source file 6 are kept. The 3 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.IsGeometricallyReducedOver`, `AlgebraicGeometry.geometricallyReduced_of_isReduced`, `AlgebraicGeometry.isGeometricallyReducedAt_of_isReduced`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
