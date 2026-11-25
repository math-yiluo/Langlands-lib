# The p-th power criteria for separability

Module `StacksFrontier.FieldTheory.Separable.TFAE`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For an extension of fields K/k with k of exponential characteristic p, separability is equivalent to preservation of linear independence by the p-th power map and to two reducedness conditions.

`Algebra.isSeparableExtension_tfae` proves the equivalence of the following conditions.

1. K/k satisfies `Algebra.StacksIsSeparableExtension` (named in the module docstring without the prefix `Stacks`), so each finitely generated intermediate field has a separating transcendence basis.
2. For every k-linearly independent subset of K, the p-th powers, indexed by that subset, are k-linearly independent.
3. K ⊗[k] k^(1/p) is reduced.
4. K is geometrically reduced over k, meaning its scalar extension to every extension field of k is reduced.

The proof uses the base-change criterion for separability to obtain geometric reducedness, then specializes to k^(1/p). For the implication from reducedness to independence, a relation among p-th powers gives a tensor with zero p-th power by taking p-th roots of the coefficients. Reducedness forces that tensor to vanish, and flatness detects the coefficients by independence after extending scalars. The final implication applies the separating transcendence basis criterion to each finitely generated subextension.

Lean represents k^(1/p) by `AdjoinPthRoots k`, using k itself with its algebra structure given by Frobenius. The linear independence test ranges over arbitrary subsets, since independence can be checked on finite subsets. The exponential characteristic includes characteristic zero with p = 1, when all four conditions hold.

The references are Tag 030W for the equivalence, Tag 030O for separability, Tag 030U for the base change, and Tag 0H71 for the transcendence basis exchange cited in the proof notes.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [030W](https://stacks.math.columbia.edu/tag/030W) | `Algebra.isSeparableExtension_tfae` | Stated for the exponential characteristic, so that characteristic zero is the case   `p = 1`, where all four conditions hold; the source assumes `p > 0`. Condition (2) quantifies over   arbitrary, not just finite, linearly independent subsets. See the module docstring. |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/FieldTheory/Separable/TFAE.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
