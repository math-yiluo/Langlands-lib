# Actual equal-rank continuations on representation vectors

This internal derived module pulls the published equal-rank rational
continuation family back along the canonical coefficient-model maps.
`equalRankVectorContinuation` is a genuinely trilinear map on the original
representation vector spaces and the row Schwartz–Bruhat test space.
It retains independent field and vector-space universes.

Surjectivity of the coefficient maps and uniqueness of rational continuation
show that its image is exactly `equalRankRationalValues`. The normalized
polynomial therefore clears every value. The canonical coefficient maps
intertwine the original actions with their model actions, so the published
simultaneous translation law gives the same law on the original vectors:
translation by a matrix of determinant absolute value `q^m` multiplies the
rational function by `X^m`.

For irreducible admissible representations, Schur's theorem supplies central
characters. At a central element whose determinant absolute value is `q^m`
with `m` a natural number, the product of the two character values is nonzero.
Linearity in the two vector arguments converts simultaneous translation into
`CentralShiftLaw` for the actual continuation and row-test translation.
For a supplied p-adic field realization, the actual inverse-uniformizer scalar
has determinant absolute value `q^(n+1)`, giving this recurrence with positive
degree equal to the common rank.

This constructs the recurrence from existing analytic conclusions and the
invariance of the quotient measure. It leaves Laurent regularity for tests
vanishing at zero, the identification of roots, and the converse occurrence
of all twist-dual parameters to the parent proof.
