# Integral multiples of rectangular diagonal corrections

This internal module defines
`HasIntegralMultipleUnitTuple O s c`: multiplication by `s` puts each
value and inverse value of the unit tuple `c` in the subring `O`.
A ratio of two tuple values then has the integral multiple `s²`.
The proof writes that multiple as the product of two known integral
elements.

For a supplied lower-unipotent factorization
`lowerBlockPair 1 x 1 = U*diag(c)*K`, suppose `U` is upper
unitriangular: it is upper triangular and every diagonal entry is
one. Also suppose `s` lies in `O`, every `s*x_ij` lies in `O`, and
every entry of `K` and `K⁻¹` lies in `O`. Then `c` has the common
integral multiple `s` in both directions. This statement holds over
any commutative ring.

The implemented proof inspects the four lower-unipotent blocks to
bound their denominators, and uses negation of the rectangle for the
inverse. Multiplication by an integral matrix preserves these
denominators entry by entry. It then writes the triangular factor as
`M*K⁻¹` and its inverse as `K*M⁻¹`. Upper unitriangularity of `U`
identifies the first factor's diagonal with `c`; the published
`diagonalUnit` identifies the inverse diagonal with `c⁻¹`. A final
coefficient-map identity records that diagonal matrices preserve this
unit-valued tuple under ring homomorphisms.

The module does not identify an adelic finite denominator by itself;
that application must supply the subring and scalar hypotheses. It
does not assert rapid decay or Mellin convergence.
