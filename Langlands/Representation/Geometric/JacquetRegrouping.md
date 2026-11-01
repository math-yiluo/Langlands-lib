# Actual Jacquet geometric-piece regrouping

Author: Worker 165.

This internal derived module regroups actual geometric-piece maps after
normalized source Jacquet restriction. Its inputs are the published actual
intersection, restriction-transitivity and geometric-piece comparisons and the
published pointwise Jacquet coefficient theorem. No classification conclusion
or irreducible-image assertion is used.

`jacquetRefinementSignedSum_eq` applies to any abelian group of values indexed by
an actual permutation and an actual target refinement. The actual target
intersection equality identifies equality of refinements with equality of their
flattened Weyl subgroups. The proof rewrites the sum over minimal-representative
subtypes as a sum over all permutations and refinements, with zero for
nonminimal permutations or other intersection refinements. Interchanging the
finite sums gives precisely the fixed-permutation coefficient of
`pointwiseJacquetCoefficientStatement`. It vanishes except at
`B.reversePermutation`; the remaining coefficient is the intrinsic product-Levi
refinement sign. This argument holds at every natural rank.

`canonicalJacquetGeometricTerm` selects a standard source shape conjugated by
the specified permutation to the flattened target refinement, or gives the zero
map when no such standard source exists. The source uniqueness theorem proves
that every actual conjugacy witness computes this same integer-linear map.
The choice therefore adds no mathematical premise.

`geometricPieces_comp_jacquet_signedSum` uses the actual map comparison
`geometricPieceK0_comp_jacquetK0` for each piece. Flattened intersection
conjugacy gives its source witness, so each summand is the canonical term at its
permutation and target refinement. The generic regrouping theorem then
identifies the entire signed map sum with the refinement sum at the single
surviving reversal. All maps act on the full exact finite-length smooth
Grothendieck groups, with independent field and carrier universes and saturated
carriers. This module does not assert that the survivor equals the transported
reversed product-Levi Aubert operator; that requires the separate actual
outer-reversal comparison.
