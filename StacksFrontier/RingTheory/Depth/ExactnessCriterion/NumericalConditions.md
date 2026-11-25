# Necessary rank and depth conditions for exact free complexes

Module `StacksFrontier.RingTheory.Depth.ExactnessCriterion.NumericalConditions`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves the numerical conditions forced by exactness in the Buchsbaum–Eisenbud criterion over a Noetherian local ring R. It also establishes the localization and acyclicity steps used in the converse.

`Numerical` and `NumericalMat` give the same predicate on linear maps and matrices, respectively. For the map from degree k + 1 to degree k, the exterior rank must be the alternating sum of the free ranks from k + 1 through e + 1, and the depth of R along the ideal of rank-sized minors must be at least k + 1.

`rank_eq_of_exact` and `le_depth_detIdeal_of_exact` prove these two conditions for all k ≤ e when successive maps compose to zero below e, the map at e is injective, and all intervening terms are exact. `numerical_zero_iff` gives the single-map equivalence between injectivity and the numerical condition.

The rank calculation localizes at associated primes, where the ring has depth zero and the exact complex yields the alternating ranks. Larger minors vanish at all those localizations and hence vanish over R. For the depth bound, prime avoidance supplies a nonzerodivisor common to the minor ideals. Reduction modulo it preserves exactness in the higher spots, so induction on the shortened complex gives a regular list to lift and extend by that nonzerodivisor.

`numericalMat_map_atPrime` preserves both conditions at any prime of a local ring. Positive depth gives a nonzerodivisor in the minor ideal, preserving the matrix rank, and flat localization preserves the needed depth bound. `ker_eq_range_of_forall_atPrime` gives exactness in degrees 1 through E + 1 for a complex of finite free modules vanishing above E + 1 over a Noetherian local ring of depth at least E + 1. Its hypothesis `hloc` supplies exactness in those degrees at every nonmaximal prime. A failure would produce a last nonzero homology of positive depth by acyclicity, although its support at the maximal ideal forces depth zero.

References include Tag 00N1, Buchsbaum and Eisenbud, *What makes a complex exact?*, Corollary 1, and EGA 0 16.4.5 for the finite free depth bound. EGA 0 16.4.6 (iii) is cited for the case of depth zero with support at the maximal ideal.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 16.4.5 | `depth_le_depth_pi_fin` | prof(A) ≤ prof(A^k) |
| EGA | 0 16.4.6 | `not_one_le_depth_of_forall_exists_smul_eq_zero` | (iii), special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Depth/ExactnessCriterion/NumericalConditions.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 18 declarations of the source file 17 are kept. The 1 left out are not needed by the results for which the extract is made: `Stacks.Depth.BuchsbaumEisenbud.le_depth_maximalIdeal_of_numerical`.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
