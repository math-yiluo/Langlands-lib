# Generic points and dimensions of irreducible closed subsets

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.Topology`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file gives topological lemmas for finding generic points inside closed and dense open subsets, and for comparing dimensions of irreducible closed subsets.

- `exists_mem_genericPoints_of_not_isNowhereDense` says that a closed subset with nonempty interior in a `QuasiSober` space contains a generic point of an irreducible component. A component through a point in the interior has its generic point in that interior by specialization. `IsGenericPoint.mem_of_isOpen_of_dense` gives membership of a generic point of the whole space in every dense open.
- `topologicalKrullDim_coe_eq_height` identifies the Krull dimension of an irreducible closed subset with its height in the poset of irreducible closed subsets. The proof compares order embeddings between the irreducible closed subsets of the subspace and the lower interval in the ambient poset, using a private lemma that an irreducible subset stays irreducible in a larger subspace. `topologicalKrullDim_coe_lt_coe_of_lt` shows strict increase under strict inclusion if the smaller subset has finite dimension.

These lemmas are used in Tag 054X and Tag 0554.

## Watch for

- The module docstring also lists a transport of nowhere density along homeomorphisms, nowhere density of a proper closed subset of an irreducible space, and a lower bound on the number of irreducible components of a space covered by finitely many closed subsets. The file holds none of these; its section on nowhere density is empty.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/NowhereDenseFibres/Topology.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 8 declarations of the source file 5 are kept. The 3 left out are not needed by the results for which the extract is made: `Homeomorph.isNowhereDense_preimage_iff`, `isNowhereDense_of_isClosed_ne_univ_subtype`, `le_ncard_irreducibleComponents_of_isClosed_cover`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
