# The kernel of a full Tate evaluation

Author: Worker 1730.

This internal construction is derived directly from the published full positive-index
inverse limit. For any commutative group object over a scheme, any test scheme, and
any positive index n, multiplication by n identifies the full Tate group with the
kernel of evaluation at n. It needs no divisibility, finite-rank or geometric premise.

For a coherent family x with x_n = 0, the underlying section of x_(n*i) is killed
by i, because its transition to x_n is i times that section. Use this section as
the i-coordinate of a new family y. Transition compatibility follows from that
of x and (n*k)/(n*i) = k/i. The transition from n*i to i gives n*y_i = x_i.
Conversely, the n-coordinate of n*y vanishes by the level annihilation lemma.
The published `full_eq_zero_of_nsmul_eq_zero` proves injectivity, giving the
additive equivalence `fullEvaluationKernelEquiv`.

The scope is the exact full predicate `fun _ => True`; no statement about a
prime-to subset of indices is claimed. This provides the projection-kernel
comparison needed in commensurable lattice realization. Evaluation surjectivity
is reused separately from `IntegralReflectionAlgebra.full_evaluation_surjective_at`.
