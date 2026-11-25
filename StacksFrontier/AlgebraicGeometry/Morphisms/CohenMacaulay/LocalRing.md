# Cohen–Macaulayness and depth of local rings

Module `StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file relates Cohen–Macaulayness of a local ring to its depth as a module and transports the condition across ring equivalences.

`isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay` says that a Noetherian local ring is Cohen–Macaulay exactly when it is a maximal Cohen–Macaulay module over itself. It identifies support dimension with Krull dimension and compares the depth supremum in the ring predicate with `Module.stacksDepth`. `isCohenMacaulayLocalRing_iff_of_ringEquiv` then transports the ring predicate along a ring equivalence between Noetherian local rings.

The module docstring also lists a result on depth along a surjective algebra map of local rings, which the file does not contain.

Tag 00N8.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/CohenMacaulay/LocalRing.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 3 declarations of the source file 2 are kept. The 1 left out are not needed by the results for which the extract is made: `Module.depth_eq_depth_self_of_surjective_algebraMap`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
