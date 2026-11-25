# Normality passes to the source of an open immersion

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.NormalFibre`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

One result on normal schemes.

- `AlgebraicGeometry.isNormal_of_isOpenImmersion`: for an open immersion `j : X ⟶ Y` with `Y` normal, `X` is normal. The stalk maps of `j` are isomorphisms, so each local ring of `X` is, like that of `Y` at the image point, an integrally closed domain. This is a version of Tag 033J for an arbitrary open immersion rather than an open subscheme.

## Watch for

- Normality is the library's `IsNormal`: every local ring is an integrally closed domain.
- The module docstring announces that the fibres of a normal morphism (Tag 0390) are geometrically normal and that a normal morphism is flat with geometrically reduced fibres. The file holds none of these; its namespace `Scheme.Hom` is empty.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/FiniteOverSmooth/NormalFibre.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 8 declarations of the source file 1 are kept. The 7 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.Scheme.Hom.IsNormal.flat`, `AlgebraicGeometry.Scheme.Hom.IsNormal.geometricallyReduced`, `AlgebraicGeometry.Scheme.Hom.IsNormal.isGeometricallyNormal_fiber`, `AlgebraicGeometry.Scheme.Hom.fiberι_cast_asFiber`, `AlgebraicGeometry.Scheme.Hom.geometricallyReduced_of_isGeometricallyNormal`, `AlgebraicGeometry.Scheme.Hom.isGeometricallyNormalAt_of_fiberι`, `AlgebraicGeometry.isNormal_spec_of_isIntegrallyClosed`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- The one reference to EGA or SGA of the source, written as an attribute of that library, belonged to a declaration left out; none is listed above.
