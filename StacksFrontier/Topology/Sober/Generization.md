# Generizations and generic points of components

Module `StacksFrontier.Topology.Sober.Generization`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

In a sober space the generic points of irreducible components are exactly the points with no proper generization.

`forall_specializes_eq_of_mem_genericPoints` proves the forward direction in a `T0Space`. The closure of a generization contains the component and is irreducible. Maximality makes the closures equal, and the T₀ axiom identifies the points. `mem_genericPoints_of_forall_specializes_eq` also assumes `QuasiSober`, so a component through the point has a generic point that specializes to it. `mem_genericPoints_iff_forall_specializes_eq` combines the directions.

In the infinite cofinite topology cited in the comments, singleton closures are singletons and the whole space is the unique irreducible component, so quasi-sobriety matters for the converse. The module docstring also lists the same criterion for the components of a closed subset, which the file does not contain.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Topology/Sober/Generization.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 4 declarations of the source file 3 are kept. The 1 left out are not needed by the results for which the extract is made: `TopologicalSpace.exists_isGenericPoint_irreducibleComponents_iff`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
