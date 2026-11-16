# Projection of a split maximal torus onto the coroot quotient

This internal construction continues the torus part of Conrad, *Reductive group
schemes* (2014), Theorem 5.3.1, pp.160–163, using the target defined in
[CorootTorusQuotient](CorootTorusQuotient.md). The registered source is
`conrad-2014-reductive-group-schemes` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`).

`corootProjection` is an actual homomorphism from the coordinate split torus to
the diagonalizable group on its coroot-annihilator lattice. It uses the inverse
of the diagonalizable split-torus comparison followed by character restriction
along the lattice inclusion. `corootProjection_points` proves its formula on
every test scheme: an annihilating character evaluates as the monomial with its
integer coordinate exponents.

When the root datum's pairing is the integer coordinate dot product, each
fixed-exponent actual coroot homomorphism is killed. The proof applies the
all-test formula and the published coordinate cocharacter formula, combines
powers into their dot-product exponent, and uses the defining annihilator
condition to make that exponent zero. The all-test identity yields the equality
of actual group-scheme homomorphisms `coroot_comp_corootProjection`. These results
allow any commutative coefficient ring, including nonreduced rings and the zero
ring; the coordinate pairing premise is stated explicitly.
