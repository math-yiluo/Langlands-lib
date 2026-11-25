# Local fibre dimension at generic points of components

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.FibreDimension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

At the generic point of a component of a scheme locally of finite type over a field, the local topological dimension equals the dimension of the component.

`topologicalKrullDimAt_eq_closure_of_mem_genericPoints` gives this equality because the point lies in just the one component, its closure. `topologicalKrullDimAt_eq_of_isClosedImmersion_genericPoints` compares a point and its image under a closed immersion. Both schemes have structure maps locally of finite type to the spectrum of the same field. When the two points are generic in components, the closed embedding identifies their closures and preserves their dimensions.

`exists_nat_topologicalKrullDimAt_fiber_of_mem_genericPoints` assumes that f is flat and locally of finite presentation and that the point viewed in its fibre is generic in a component. It gives a natural number equal to the local fibre dimension, using the fibrewise dense union of opens of specified relative dimension.

Here the local dimension is the library's `stacksTopologicalKrullDimAt`, the minimum of the dimensions of open neighbourhoods of the point.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/NowhereDenseFibres/FibreDimension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
