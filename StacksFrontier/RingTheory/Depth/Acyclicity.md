# The acyclicity lemma

Module `StacksFrontier.RingTheory.Depth.Acyclicity`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file bounds the depth of homology in the greatest degree where a bounded complex fails to be exact. All depths are taken at the maximal ideal of a Noetherian local ring R.

`Module.one_le_depth_homology_of_forall_le_depth_of_isGreatest_not_exactAt` treats a chain complex of finite R-modules in natural-number degrees. Its terms vanish above e, and the term in degree j has depth at least j for j ≤ e. If i > 0 is the greatest degree at which exactness fails, the homology in degree i has depth at least one.

The proof applies the short exact sequence depth inequalities in `Module.min_depth_le_depth_of_exact`. Descending from the zero terms, exactness above i identifies cycles with boundaries and gives the cycles in degree j > i depth at least j + 1. The boundaries in degree i then have depth at least two. Its cycles have depth at least one because they lie in a module of positive depth, so the cycles modulo boundaries have depth at least one. A linear equivalence transfers this estimate to the categorical homology.

The hypothesis `hi` states that i is the greatest nonexact degree. The argument uses its upper bound, namely exactness in all higher degrees. The positivity hypothesis is essential. Over a field, a complex supported only in degree zero with a nonzero term there has degree-zero homology of depth zero.

References include Stacks Project Tag 00N0 and Peskine and Szpiro, *Dimension projective finie et cohomologie locale*, Lemma 1.8.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00N0](https://stacks.math.columbia.edu/tag/00N0) | `Module.one_le_depth_homology_of_forall_le_depth_of_isGreatest_not_exactAt` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Depth/Acyclicity.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
