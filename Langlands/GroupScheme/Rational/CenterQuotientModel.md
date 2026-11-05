# A supplied algebraic model of the literal full-center point quotient

Author: Worker 1232.

This is derived infrastructure for the full-center compactness target. It
combines the actual all-test fppf kernel identity with the closed-center
representative and point-quotient homeomorphisms. It constructs neither an
algebraic center quotient nor sections of a split-torus torsor.

For an actual group-scheme map `j : A → Z` and an actual fppf quotient
`q : Z → C` of its range functor, `rationalPoints_ker_eq_range_of_fppfQuotient`
evaluates the all-test scheme-kernel identity at `Spec R`. Membership in that
kernel is exactly postcomposition with `q` being the identity point. Membership
in the range is exactly having an actual preimage in `A(R)`. This uses no
surjectivity assertion on the rational points of `q`.

Let `z : Z → M` be a closed representative of the full scheme center. Suppose
`j` factors the given central map `i : A → M`, so `j ≫ z = i`.
`schemeCenterQuotientPointMap` transports `q(R)` to the literal subgroup
`schemeCenterPoints M` through `schemeCenterRepresentativeHomeomorph`.
Its kernel is exactly `centralRationalPointImage i hi`, as follows by evaluating
the factorization and using injectivity of the representative equivalence.
The numerator retains all scheme-center points, without smoothness,
connectedness, or reducedness conditions on `Z`.

Assume also that `R` is a topological local ring with continuous multiplication
and open units, that `M` and `C` are affine, and that `q` has algebraic open
sections at every actual `R`-point of `C`. The represented center `Z` is affine
because it is closed in `M`. The point-map theorem for open sections and the
center representative homeomorphism prove that the transported map is a
quotient map for exactly the inherited center topology and the canonical
affine point topology. `centralPointQuotientModelHomeomorph` then constructs
the multiplicative homeomorphism from the literal `CentralPointQuotient i hi`
with its explicitly selected quotient topology to `C(R)`.

The existence of `Z/A`, the required open sections for a split-torus quotient,
and compactness of `C(R)` remain separate obligations for the unconditional
`CenterSplitComponentCompactnessStatement`.
