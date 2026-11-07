# Degree coordinates on inertia invariants of coinduction

This internal algebraic construction supports the Euler-factor induction proof.
It uses Mathlib's actual equivariant-function coinduction and fixed-vector
subspaces, with arbitrary coefficient field and independent group and carrier
universes.

Let the two groups have integer degree homomorphisms, with a homomorphism
`ι : H → G` multiplying degree by a positive integer `f`. Choose arbitrary
elements `Φ` and `η` of degree one in the two groups. Evaluation at
`Φ^(-i)`, for `0 ≤ i < f`, identifies the invariants under the kernel of
the ambient degree with `f` copies of the source degree-kernel invariants.

The proof first shows that invariant equivariant functions have the same
value at elements of equal degree, and that their values lie in source
invariants. Euclidean division gives the unique decomposition
`m = f*q - r`, with `0 ≤ r < f`. Reconstruction sends an element of degree
`m` to `ρ(η^q) v_r`. Equal-degree source elements act identically on
source invariants, which proves equivariance of reconstruction. Evaluation
and reconstruction are inverse. No continuity, finite-index, or
finite-dimensional assumption is used in this comparison.

This is a derived construction, not a new assertion from the literature.
The subsequent cyclic-operator comparison and specialization to actual
local Weil groups are separate steps.
