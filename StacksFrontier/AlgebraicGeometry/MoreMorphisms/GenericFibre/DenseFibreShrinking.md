# The complement of an open set is nowhere dense when it is dense

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.DenseFibreShrinking`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

One lemma of topology.

- `AlgebraicGeometry.isNowhereDense_compl_iff`: for an open subset `W` of a topological space, the complement `Wᶜ` is nowhere dense if and only if `W` is dense. As `Wᶜ` is closed, it is nowhere dense exactly when its interior, the complement of the closure of `W`, is empty.

## Watch for

- The module docstring announces that an open which is dense in the generic fibre of a finite type morphism is dense in the fibres over a nonempty open of the base (the open-complement form of Tag 054X). The file does not hold it; the lemma above is the topological step it rests on.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/GenericFibre/DenseFibreShrinking.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 2 declarations of the source file 1 are kept. The 1 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.exists_open_dense_fiber_preimage`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
