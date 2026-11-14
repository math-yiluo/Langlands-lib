# Rational root points outside the second cyclic weight tail

This internal supporting unit works at arbitrary universe `u`, over every field,
for a smooth affine group scheme `G` and a homomorphism `i` from a split torus.
No reductivity, maximal splitness, perfection, infinitude, or algebraic closure
is required. Its actual root and cyclic weight subgroup functors are the
existing Library functors on all test schemes.

The exact nonzero root weight `a` occurs in the Lie support of `U_a` and does
not belong to the cyclic tail of multipliers at least two. Exact semigroup Lie
images and split-torus weight independence therefore show that `U_a` cannot
lie in that tail. The cyclic filtration theorem supplies the first vector
quotient of a closed representative of `U_a`. Its vector dimension is positive:
dimension zero would make its quotient map trivial on every test and put
`U_a` in the second tail.

The second tail has a smooth closed split-unipotent representative. The
canonical morphism from that representative into the representative of `U_a`
represents the actual quotient kernel. The published split-unipotent affine
torsor theorem lifts a nonidentity rational vector point to an actual rational
point of `U_a`. Its image in the vector quotient proves exclusion from the
entire second cyclic tail.

For every natural number `n` with `2 ≤ n`, the root subgroup `U_(n*a)` lies
in the second tail by the cyclic-root comparison and semigroup monotonicity.
The same rational point therefore lies outside `U_(n*a)`.
`rationalRootPointOutsideMultiple` chooses a point with its membership and
exclusion proofs. This extends the earlier algebraically closed witness by an
actual rational quotient lift, and supplies no integral lifting assertion.

All results are derived from the imported Library theorems; this unit makes
no additional original-literature assertion.
