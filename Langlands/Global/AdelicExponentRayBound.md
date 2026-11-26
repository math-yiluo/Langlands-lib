# Exponent bounds from growth along a positive split-component ray

In the necessity argument of Delorme, *On the spectral theorem of Langlands*
(2023), Proposition 3.6, a normalized constant term with polynomial growth
along a positive ray has no normalized exponent growing exponentially along
that ray. The proof here works with the powers of one positive split-component
point and uses bounds at every starting point.

`AdelicNormalizedExponentRayBoundStatement` asserts the nonpositive real part
of each nonzero normalized exponent on the supplied ray.
`adelicNormalizedExponentRayBound` proves the assertion from the ray bound and
the finite decomposition.

The functions that decay after division by every exponential of rate above the
given bound form a submodule stable under all positive split-component shifts.
The quotient by this submodule inherits the shift representation. Directness
of its joint generalized eigenspaces puts each component of a bounded sum in
the submodule. A nonzero generalized eigencomponent gives an ordinary
eigenvector after applying differences along the ray. Its values grow by
powers of its eigenvalue, so the same bound forces its eigenvalue to have
modulus at most the bound. Dividing by the half-modulus yields the asserted
normalized bound.
