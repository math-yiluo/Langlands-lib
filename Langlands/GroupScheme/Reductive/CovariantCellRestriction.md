# Restriction and dimension bounds for entire covariant spaces

Worker 669 derives these constructions from the actual coordinate pullback,
covariance on all relative schemes, localization separation, and finite
coefficient linear algebra. No external structural theorem is used.

Let `G,H,U` be actual affine group schemes over any field `k : Type u`.
Supply morphisms `i : H → G`, `j : U → G`, a coordinate `χ` of `H`,
and a nonzerodivisor `q` of the coordinate algebra of `G`. Assume every
point where `q` is a unit factors as `i(a) j(u)` on the original relative
scheme test. The factorization includes nonaffine and nonreduced tests.

`covariantCellRestriction` restricts the entire left-covariant coordinate
space of weight `χ` to `U`, using the actual Hopf-coordinate pullback of
`j`. It is injective: equal restrictions give equal values on `j(u)`;
left covariance gives equal values on every product `i(a) j(u)`; and
localization separation for the nonzerodivisor `q` gives equality in the
original coordinate algebra. This requires no reducedness, algebraic
closure, finite type, unipotence, or character hypothesis.

Now supply a polynomial coordinate algebra equivalence
`e : algebra U ≃ₐ[k] MvPolynomial σ k`, where the variable type has an
independent universe. `covariantPolynomialRestriction` is restriction in
these coordinates and is injective. For any finite set `S` of monomials,
`covariantCellCoefficients` records their coefficients in that polynomial.
This definition alone does not assert any bound or injectivity.

If the restriction of every element of the entire covariant space is
supported in `S`, equality of those coefficients gives equality of every
coefficient: coefficients outside `S` vanish by the support bound.
Restriction injectivity then makes this finite coefficient map injective.
It follows that the entire covariant space is finite dimensional and has
dimension at most `S.card`.

The degree-bound corollary takes a finitely supported exponent vector `N`.
If every restricted polynomial has multiset of degrees at most
`N.toMultiset`, its support lies in the finite interval of monomials
`m ≤ N`. Counting that interval gives the bound
`∏ a ∈ N.support, (N a + 1)`. Zero degree and empty support are included.

For a covariant coordinate `f`, its previously constructed singleton
regular span `affineCovariantSocle G f` lies inside the entire covariant
space. If its dimension is at least `S.card`, the restriction upper bound
forces equality. This proves an entire-space equality from finite
coefficient bounds and an independently supplied dimension lower bound.
It assumes neither that equality nor irreducibility of the entire space.

Finally assume `U` is unipotent, `f` is right invariant under `j`, and its
counit is one. The existing socle irreducibility theorem and the proved
equality give irreducibility of the actual regular representation on the
entire covariant space, for every supplied finite basis. Stability retains
every affine test algebra. This last result is conditional on the uniform
support bound and socle dimension bound; those bounds are not constructed
for general Steinberg weights here. Polynomial cell coordinates and the
geometric factorization also remain supplied. The universal
`SteinbergBigCellStatement` is not proved by this module.
