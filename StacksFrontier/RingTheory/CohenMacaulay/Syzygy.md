# Depth of a syzygy over a Cohen–Macaulay local ring

Module `StacksFrontier.RingTheory.CohenMacaulay.Syzygy`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The depth lemma controls the kernel of a surjection from a finite free module. Over a Cohen–Macaulay local ring it gives a dichotomy between a strict increase in depth and both modules attaining the ring dimension.

## Main result

`Module.IsMaximalCohenMacaulay.depth_lt_depth_or_isMaximalCohenMacaulay_of_exact` assumes a Noetherian local ring `R` with `Module.IsMaximalCohenMacaulay R R` and a short exact sequence `0 → K → F → M → 0` with `F` finite free and `M` nonzero. At the maximal ideal, either `depth(M) < depth(K)` or both `K` and `M` are maximal Cohen–Macaulay, meaning their depths equal `dim R`.

The private helper `depth_le_depth_of_free` gives a lower bound for the depth of a finite free module by the depth of its Noetherian base ring, along any ideal. It inducts on the rank using the depth inequality for a split short exact sequence.

## Proof idea

The third depth inequality for a short exact sequence gives `min(depth(F), depth(M) + 1) ≤ depth(K)`, and the support-dimension and free-module bounds give `depth(M) ≤ dim R ≤ depth(F)`. This forces a strict increase when `depth(M) < dim R`, and when `depth(M) = dim R` the support-dimension bound forces equality for a nonzero kernel.

## Scope

Lean's dichotomy takes `[Nontrivial M]` to restrict to the nonzero quotient case. A zero kernel is allowed and has depth `⊤`, giving strict increase. Short exactness is given by an exact pair of linear maps with the left map injective and the right map surjective. Finiteness of the kernel and quotient follows from these hypotheses and finiteness of `F`.

## References

Tag 00NE, with Tag 00LX for the depth inequalities and Tag 00LK for the support-dimension bound. SGA 2 X 2.1 concerns the free-module bound.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00NE](https://stacks.math.columbia.edu/tag/00NE) | `IsMaximalCohenMacaulay.depth_lt_depth_or_isMaximalCohenMacaulay_of_exact` | Cohen-Macaulayness of the Noetherian local ring `R` is `Module.IsMaximalCohenMacaulay R R`, i.e. `depth_𝔪(R) = dim R` (Definition 00N8); `R^{⊕n}` is an arbitrary finite free module `F`; the alternative `M = 0` is the hypothesis `[Nontrivial M]`; and `depth(K) = depth(M) = d` is maximal Cohen-Macaulayness of `K` and of `M`. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 2 X 2.1 | `depth_le_depth_of_free` | inequality depth O_{U |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/CohenMacaulay/Syzygy.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
