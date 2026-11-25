# The completion square of a DVR extension

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppCompletionSquare`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A local map A → B of discrete valuation rings induces a map Â → B̂ between the completions at their respective maximal ideals. This file builds the square of ring maps, extends it to fraction fields, and transports the ramification and residue-field data used in Epp’s theorem.

- `adicCompletionMap` constructs the map of completions. The theorem `adicCompletionMap_comp_algebraMap` proves commutativity of the square, and `isLocalHom_adicCompletionMap` proves that the induced map is local. For a DVR extension A → B, the induced map is also injective and gives a DVR extension.
- `ramificationIdx_adicCompletionMap` gives e(B̂/Â) = e(B/A). The definition `adicCompletionFractionFieldMap` extends the map of completions to their fraction fields, with `algebraAdicCompletionFractionFieldMap` supplying the corresponding algebra structure.
- `isSeparableExtension_residueField_adicCompletionMap` carries separability of the residue extension to the completions. For a noetherian local ring, further lemmas carry its residue characteristic to the completion.
- `tame_adicCompletionMap` transports the disjunction used in the tame case. It applies when the base residue characteristic is zero, or when it is coprime to the ramification index and the residue extension is separable.

Locality maps each power of the maximal ideal of A into the corresponding power for B. The compatible maps on quotient rings give `adicCompletionMap` by passage to the limit. A uniformizer factorization carries over to the completions and gives the index calculation. The isomorphisms on residue fields transport separability via formal smoothness.

Locality suffices for construction of the completion map. The index and fraction-field results assume a DVR extension. The algebra structures on the completions and their fraction fields are supplied as named definitions for local use. The module docstring also lists a result carrying perfectness of the residue field to the completion, which the file does not contain.

The completion square is used in step 3 of Tag 09F9. The file also cites Tag 0AP1 and Tag 09EJ in connection with the maximal-ideal completions.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppCompletionSquare.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 29 declarations of the source file 28 are kept. The 1 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.perfectField_residueField_adicCompletion`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
