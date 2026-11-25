# Adic formal smoothness under isomorphisms of arrows

Module `StacksFrontier.RingTheory.FormallySmooth.AdicArrowIso`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Adic formal smoothness transports when both rings of a homomorphism are replaced by isomorphic rings and the target ideal is carried along.

`RingHom.FormallySmoothNAdic.of_arrowEquiv` takes isomorphisms eR and eS at the source and target that form a commuting square with φ and φ′. It transfers formal smoothness of φ for the n-adic topology to φ′ for the topology defined by the image of n under eS. `RingHom.FormallySmoothNAdic.of_arrowEquiv_of_map_eq` uses an explicit equality identifying that image with a chosen ideal n′, as for corresponding maximal ideals.

The proof precomposes the two given maps with the isomorphisms, transports the power-kernel condition, and composes the lift with the inverse of eS. The source and target may change universes while the test ring keeps its universe.

Stacks Project, Tag 07EE and Tag 07NI.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/FormallySmooth/AdicArrowIso.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
