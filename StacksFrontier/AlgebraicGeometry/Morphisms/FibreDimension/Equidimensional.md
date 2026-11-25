# Local fibre dimension on an open of constant relative dimension

Module `StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

`topologicalKrullDimAt_fiber_eq_of_relativeDimension`: let `f : X ⟶ S` be locally of finite type and U an open of X such that the restriction `U.ι ≫ f` has `RelativeDimension` d. Then for every x ∈ U the fibre of f over f(x) has local topological Krull dimension d at `f.asFiber x`.

The proof first treats a morphism of relative dimension d: the fibre through x is then equidimensional of dimension d, and for a scheme locally of finite type over a field this gives the local dimension at every point (`topologicalKrullDimAt_eq_of_equidimensional`, from another file). Precomposition with the open immersion of U does not change the local fibre dimension (`fiberDimensionAt_comp_openImmersion`).

`RelativeDimension` imposes equidimensionality and the specified dimension on nonempty fibres.

The module docstring also lists the converse comparison over a field, the inheritance of relative dimension along open immersions and a statement over a one-point base; the file contains none of these, and the comparison it names first is declared in another file.

Tag 0A21 for local dimension in terms of components and Tag 02NJ for relative dimension.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/FibreDimension/Equidimensional.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 7 declarations of the source file 2 are kept. The 5 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.RelativeDimension.comp_isOpenImmersion`, `AlgebraicGeometry.RelativeDimension.of_comp_isOpenImmersion`, `AlgebraicGeometry.equidimensional_of_topologicalKrullDimAt_eq`, `AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_cast`, `AlgebraicGeometry.topologicalKrullDim_eq_of_relativeDimension`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
