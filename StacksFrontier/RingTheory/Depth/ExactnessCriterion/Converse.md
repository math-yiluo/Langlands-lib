# The Buchsbaum–Eisenbud criterion and its converse

Module `StacksFrontier.RingTheory.Depth.ExactnessCriterion.Converse`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves that rank and determinantal depth conditions suffice for exactness of a finite free complex over a Noetherian local ring. It combines this converse with the necessary conditions established in the preceding development.

`LinearMap.injective_and_exact_iff_forall_rank_eq_and_le_depth_minors` takes free modules of ranks n₀ through nₑ₊₁ and maps φₖ from degree k + 1 to degree k. The hypothesis `hφ` says successive maps compose to zero for k < e. Injectivity of φₑ and exactness in degrees 1 through e are equivalent to these two conditions holding for every k ≤ e.

- The greatest r for which the r-th exterior power of φₖ is nonzero is the integer alternating sum of the free ranks from nₖ₊₁ through nₑ₊₁, starting with a positive sign.
- The depth of R along the ideal of r-by-r minors of φₖ is at least k + 1.

The proof translates the conditions to matrices. The converse inducts on the height of the maximal ideal, with an inner induction on the top degree. Localization at each nonmaximal prime preserves the numerical conditions and reduces the height. When the top determinantal ideal is proper, its depth bound gives enough maximal-ideal depth to apply the acyclicity lemma. When the ideal is the unit ideal, a unit minor makes the top differential a split injection. Removing its image shortens the complex and preserves the remaining rank and minor data. The one-map case uses the injectivity criterion for a full-column-rank matrix whose minor ideal contains a nonzerodivisor.

Exactness is asserted in positive degrees. The depth in the criterion is measured along each minor ideal, so the unit ideal satisfies the bound with infinite depth.

References include Tag 00N1 and Buchsbaum and Eisenbud, *What makes a complex exact?*, Corollary 1.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00N1](https://stacks.math.columbia.edu/tag/00N1) | `LinearMap.injective_and_exact_iff_forall_rank_eq_and_le_depth_minors` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Depth/ExactnessCriterion/Converse.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
