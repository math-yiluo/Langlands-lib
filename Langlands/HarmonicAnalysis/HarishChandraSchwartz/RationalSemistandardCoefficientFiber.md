# Actual coefficient fibers in the intrinsic semistandard model

This internal adapter identifies the coefficient carrier of Waldspurger's
V.3 comparison with the intrinsic all-representative product-induced fibers
of VI.1 as defined in `RationalSemistandard.OrbitSections`. The index is the
published `SemistandardSpectralIndex`. The cocharacter presentation is an
auxiliary witness for its actual all-test parabolic, Levi and radical.

`comparisonParabolic` presents the original parabolic over any cocharacter
whose actual centralizer is the intrinsic Levi. Its Iwasawa factorization
comes from the given `CompactData`. This allows the target of a rational
conjugation to keep its own intrinsic index and parabolic independently of
the chosen anchor for the conjugate Levi.

`intrinsicInducing` is pullback along the identity on points of the two equal
literal Levi subgroups. `fiberEquiv` applies the actual product left
translation at the identity point, with compactness of the two parabolic
quotients supplied by the same factorization. It then applies the inverse
of `productInducedCoefficientLeviEquiv`, the published comparison from
normalized product induction to positive-Levi induction. The codomain is
therefore precisely the normalized product-induced coefficient object used
by the intrinsic orbit sections, with its full external product action.
These constructions apply to arbitrary smooth inducing objects, including
the literal twists and the irreducible admissible orbit representatives.
