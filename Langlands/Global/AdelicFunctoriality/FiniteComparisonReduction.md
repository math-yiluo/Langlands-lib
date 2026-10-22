# Surjectivity and the remaining finite local-degree comparison

This module proves that the canonical `finiteTensorMap` from `Norm.lean` is
surjective. It retains arbitrary number fields in independent universes and
uses their actual height-one primes and adic completions. It also proves that
bijectivity of this map is equivalent to equality between the sum of the
completed local degrees and the global extension degree.

The reverse degree inequality is not proved here. Consequently this module
does not prove `CompletedTensorComparison`, the complete `NormCompatibility`
target, or unconditional descent of the norm to idele classes.

The proof begins with the actual normalized adic absolute value of each prime.
A nonzero element of the prime ideal has absolute value less than one, so this
absolute value is nontrivial. If two such absolute values are equivalent,
their sets of integers of absolute value less than one coincide. These sets
are the original prime ideals, so the primes are equal. Thus distinct primes
give inequivalent absolute values.

`finiteWithAbsEmbedding` is the genuine field embedding into its adic
completion, with the source equipped with the normalized absolute value.
Mathlib's norm formula makes it an isometry. The original field is dense in
its completion, so this embedding has dense range.

`denseRange_finiteAbove` applies Mathlib's weak approximation theorem
`AbsoluteValue.denseRange_algebraMap_pi` to the finite family of actual
primes above the chosen base prime. Applying the continuous dense embeddings
coordinatewise gives density of the diagonal field image in the product of
the actual completions. No abstract product presentation or unproved
approximation hypothesis is supplied.

The image of `finiteTensorMap` contains this diagonal image: `1` tensor `y`
maps to the family of embedded copies of `y`. Its range is a finite-dimensional
linear subspace over the complete, nontrivially normed base completion.
Mathlib's closedness theorem for such subspaces makes this dense range the
whole product, proving `finiteTensorMap_surjective`.

Surjectivity gives `finiteLocalDegree_sum_le`: the sum of the completed local
dimensions is at most the global extension degree. Here finite-dimensional
base change computes the dimension of the tensor product, and the dimension
of a finite dependent product is the sum of the dimensions of its factors.
Conversely, a lower bound in the other direction makes the surjective map
bijective by the finite-rank form of the Orzech property.
`finiteTensorMap_bijective_iff_degree_sum` states the exact equivalence, and
`finiteTensorMap_bijective_of_degree_lower_bound` exposes the sufficient
remaining obligation. These are reductions, not proofs of the degree equality.

`finitePlacesAboveEquivPrimesOver` constructs an equivalence between the
actual height-one primes in `FinitePlacesAbove L p` and Mathlib's subtype
`p.asIdeal.primesOver (𝓞 L)`. The forward map takes the underlying ideal;
the inverse uses its primeness and the nonzeroness forced by contraction
to the nonzero prime `p`. Both inverse laws are definitional. This is an
internal indexing comparison, not a classification of completed fields.

Reindexing `Ideal.sum_ramification_inertia_eq_finrank` along this equivalence
and using `IsFractionRing.finrank_eq` proves
`finitePlacesAbove_sum_ramification_inertia`: the sum of the actual global
ramification-inertia products over `FinitePlacesAbove L p` is `[L : K]`.
This identity concerns global integer-ring invariants. It does not identify
those products with the degrees of completed extensions.

`finiteTensorMap_bijective_of_local_degree_bounds` sums explicit per-place
hypotheses `e(q/p) * f(q/p) ≤ [L_q : K_p]` and applies the earlier lower-bound
criterion. These hypotheses are not proved in this module. In particular,
this final criterion remains conditional and does not discharge the
unconditional tensor-comparison task.

The source through `finiteTensorMap_bijective_of_degree_lower_bound` is reused
from Worker 50's shared draft. Worker 52 added the equivalence of prime-index
types, the global ramification sum, and the conditional per-place criterion.
All those additions are internal deductions from the cited Mathlib results.

The original mathematical construction is Andre Weil, *Basic Number Theory*,
second edition (1973), Chapter III section 4, Theorem 4 and Corollary 3,
printed pp. 56-58 (PDF pp. 73-75).
Registered original: `weil-1973-basic-number-theory`, SHA256
`32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
These passages were read. This module implements only the surjectivity
portion and the degree reduction of that comparison, using the pinned
Mathlib weak approximation and finite-dimensional topology theorems as
described above.
