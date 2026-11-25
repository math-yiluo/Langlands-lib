# Exact free complexes over depth-zero local rings

Module `StacksFrontier.RingTheory.Depth.ExactnessCriterion.DepthZero`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves the depth-zero case of the necessary rank and minor conditions in the Buchsbaum–Eisenbud criterion. It also develops localization and truncation lemmas for complexes written as matrices.

`Stacks.Depth.BuchsbaumEisenbud.rank_eq_and_minorIdeal_eq_top_of_injective_of_exact_of_depthZero` takes a Noetherian local ring S with its maximal ideal associated to S. Given matrices Aₖ from degree k + 1 to degree k, it assumes zero successive composites below e, injectivity of Aₑ, and exactness at the intervening terms. For each k ≤ e, the determinantal rank of Aₖ is the alternating sum of the free ranks from degree k + 1 through e + 1, and its ideal of rank-sized minors is the unit ideal.

The proof cuts off the complex above degree e + 1 using `truncRank` and `truncMat`. It then uses `exists_trivial_iso_of_exact` to put the differentials in partial permutation form by changes of basis. Pivot columns give an identity minor of rank size. Exactness makes the pivot columns of each outgoing map complementary to the pivot rows of the incoming map, giving the consecutive rank sums and hence the alternating formula.

The localization lemmas `exact_map_algebraMap_atPrime` and `injective_map_algebraMap_atPrime` preserve exactness and injectivity under entrywise localization at a prime of a commutative ring. If the localized pair is exact, `exists_smul_mem_range_of_ker_eq_range_map` clears denominators to send each original kernel element into the image by multiplication by some scalar outside the prime.

The main result uses membership of the maximal ideal in the associated primes as its depth-zero hypothesis. The input ranks and matrices may be given in all degrees, with the conditions confined to degrees at or below the stated cutoff. This is one step of the forward direction of Tag 00N1. The file also cites Buchsbaum and Eisenbud, *What makes a complex exact?*, Corollary 1.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Depth/ExactnessCriterion/DepthZero.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
