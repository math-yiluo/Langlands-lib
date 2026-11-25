# Depth inequalities for short exact sequences

Module `StacksFrontier.RingTheory.Depth.ShortExact`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file bounds each of the three depths in a short exact sequence of modules over a Noetherian commutative ring R. The depths are taken along an arbitrary ideal I of R.

`Module.min_depth_le_depth_of_exact` takes a short exact sequence 0 → A → B → C → 0, expressed as an exact pair of linear maps with the first injective and the second surjective. It assumes B is finite, which implies finiteness of A and C. Writing d for I-depth, the three conclusions are

- min(d(A), d(C)) ≤ d(B).
- min(d(B), d(A) − 1) ≤ d(C).
- min(d(B), d(C) + 1) ≤ d(A).

The proof uses Rees’ theorem to turn a natural lower bound on depth into vanishing of Ext from R/I in all lower degrees. The three estimates follow from the long exact Ext sequence, with the degree-zero case for A using injectivity on Hom. When IM = M for a finite module M, Nakayama supplies an element of I acting as the identity on M and annihilating R/I, so all these Ext groups vanish.

Subtraction is truncated in ℕ∞. The modules may live in different universes because the proof transports them to a common universe for the Ext argument.

The inequalities are Stacks Project Tag 00LX.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00LX](https://stacks.math.columbia.edu/tag/00LX) | `min_depth_le_depth_of_exact` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Depth/ShortExact.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 15 declarations of the source file 14 are kept. The 1 left out are not needed by the results for which the extract is made: `Stacks.Depth.ShortExactInequalities.isRegular_of_isWeaklyRegular`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
