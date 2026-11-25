# Depth under a ring isomorphism

Module `StacksFrontier.RingTheory.Depth.RingEquiv`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file transports ideal-relative depth between isomorphic commutative rings viewed as modules over themselves.

`Module.depth_eq_of_ringEquiv` says that for a ring isomorphism e from A to B and an ideal I of A, the depth of A along I equals the depth of B along the image of I. `Module.depth_self_eq_of_ringEquiv` gives equality of maximal-ideal depths when A and B are local rings.

The one-way bound `Module.depth_le_of_ringEquiv` follows because the isomorphism preserves the unit ideal case and sends regular sequences in I to regular sequences of the same length in its image. Applying the bound to the inverse yields equality. In the local case the isomorphism carries the maximal ideal to the maximal ideal.

The depth definition is from Tag 00LI.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Depth/RingEquiv.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
