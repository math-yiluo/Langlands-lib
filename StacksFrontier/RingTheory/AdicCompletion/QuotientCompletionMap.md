# Completion of a quotient of a local ring

Module `StacksFrontier.RingTheory.AdicCompletion.QuotientCompletionMap`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a commutative local ring R and an ideal I with R/I local, the quotient map induces a surjection on maximal-ideal-adic completions. When R is Noetherian, its kernel is the extension of I.

`quotientLevelMap` is the ring map from R/𝔪ⁿ to the quotient of R/I by the nth power of its maximal ideal. The class of a representative r maps to zero exactly when r belongs to I + 𝔪ⁿ. `adicCompletionMapQuotient` assembles these maps on coherent sequences, so that its level-n component is `quotientLevelMap` (`completionQuotientMap_val`).

`adicCompletionMapQuotient_surjective` proves surjectivity for local R and R/I. For Noetherian R, `ker_adicCompletionMapQuotient` computes the kernel as IÂ, and `nonempty_ringEquiv_adicCompletion_quotient` gives the resulting ring isomorphism between the completion of R/I and Â/IÂ, where Â is the completion of R. The file also proves `isNoetherianRing_adicCompletion` for Noetherian local R.

Surjectivity lifts a coherent sequence by choosing representatives recursively and adjusting each lift by an element of I. A kernel element has a representative in I at every level, so its image in the Noetherian local ring Â/IÂ lies in every power of the maximal ideal and vanishes by adic separatedness.

The quotient-ring form of exactness of completion is cited as Tag 00MB, and Noetherianity of the maximal-ideal-adic completion as Tag 05GH.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/AdicCompletion/QuotientCompletionMap.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 14 declarations of the source file 13 are kept. The 1 left out are not needed by the results for which the extract is made: `completionQuotientMap_algebraMap`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
