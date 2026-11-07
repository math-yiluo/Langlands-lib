# Nonvanishing of centered segment boundary polynomials

`SegmentBoundaryNonvanishingStatement` is an internal algebraic statement
supporting the square-integrable pair-factor calculation. It uses the existing
`SegmentGammaTelescoping.boundaryPolynomial`, without changing its indexing.

For a finite set `A` of complex units, a complex unit `t`, and natural numbers
`m,n` with `n ≤ m`, assume that `t` and every member of `A` have norm at most
one. Then the product over `a ∈ A` of

`∏ j : Fin (n+1), (1 - a t^(m+n-2j) X)`

does not vanish at any complex number of norm less than one.
The claim includes equality in both norm bounds and includes the empty set.

This is derived directly from the nonnegative exponents
`m+n-2j ≥ m-n ≥ 0`. Each coefficient `a t^(m+n-2j)` has norm at most one;
multiplication by an argument in the open unit disk therefore cannot give one.
It is not a statement about actual representations or certified L-polynomials.
Those identifications, the norm estimates for their parameters, and the
rank-to-length comparison remain separate obligations in any application.
