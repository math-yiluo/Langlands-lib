# A point specializing to the generic point of a component

Module `StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Embedded`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

One lemma of topology.

- `Topology.eq_of_specializes_isGenericPoint`: in a `T₀` space, let `x` be the generic point of an irreducible component `Z`. A point `y` with `y ⤳ x` equals `x`: otherwise the closure of `y` would be an irreducible closed set strictly larger than `Z`.

## Watch for

- The module docstring announces the definitions of embedded associated points of a sheaf of modules and of embedded points and components of a scheme (Tag 05AK), with the predicates of their absence. The file holds none of these; its namespace `AlgebraicGeometry` is empty.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Divisors/AssociatedPoints/Embedded.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 6 declarations of the source file 1 are kept. The 5 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.HasNoEmbeddedAssociatedPoints`, `AlgebraicGeometry.HasNoEmbeddedPoints`, `AlgebraicGeometry.IsEmbeddedAssociatedPoint`, `AlgebraicGeometry.IsEmbeddedComponent`, `AlgebraicGeometry.IsEmbeddedPoint`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
