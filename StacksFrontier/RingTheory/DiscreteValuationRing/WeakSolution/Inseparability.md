# Weak unramifiedness and the ramification index

Module `StacksFrontier.RingTheory.DiscreteValuationRing.WeakSolution.Inseparability`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For any extension of discrete valuation rings A → B in the sense of `IsExtension` (an injective local algebra map), `isWeaklyUnramified_iff_ramificationIdx_eq_one` identifies weak unramifiedness, `IsWeaklyUnramified A B`, with the length-based ramification index `(IsLocalRing.maximalIdeal B).ramificationIdx A` being one. The proof is a rewrite by `ramificationIndex_eq_ramificationIdx`, which equates the library's ramification index of the extension with this one.

`IsExtension` and `IsWeaklyUnramified` are this library's notions, from `StacksFrontier.RingTheory.DiscreteValuationRing.Solution`. The module docstring still describes the Laurent-series example of weak solutions, base change along a totally ramified extension and a Galois action, with Tags 09EP, 09ER and 09EU; the file contains none of them.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/WeakSolution/Inseparability.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 35 declarations of the source file 1 are kept. The 34 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
