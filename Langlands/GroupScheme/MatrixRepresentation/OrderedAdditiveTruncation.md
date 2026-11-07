# Bounded nilpotent tests for ordered additive-subgroup actions

For an actual group-scheme representation `rho : G -> GL(n)` over a field
`k` and a finite ordered family of supplied maps `x_i : Ga -> G`, this
derived unit considers the original action at `x_0(t_0) ... x_(d-1)(t_(d-1))`.
The subgroup images need not commute. All products preserve their given
order, and the rightmost endomorphism acts first on column vectors.

`coefficientOperator a` is the ordered product of the actual divided powers
at the exponents `a i`. `orbitPolynomial v` applies the ordered polynomial
matrix to the constant vector `v`. The coefficient formula follows from
`OrderedAdditiveProducts.orderedCoefficients_eq_prod`, and evaluating this
polynomial gives the original affine action over every commutative test
algebra.

Given a finitely supported bound `N`, `universalOrbit N v` evaluates at the
universal tuple in `PolynomialBoxQuotient.boxAlgebra N`. Each parameter has
vanishing power `N i + 1`. Applying its retained coefficient functional
recovers exactly `coefficientOperator a v` for each `a <= N`. This is an
actual action on a commutative test algebra, including its nilpotent
elements.

Every tuple `t` in a commutative test algebra `A` satisfying those same
power relations factors through this universal algebra. Expanding an
element of the universal algebra in its finite monomial basis proves
`linearFunctional_affineAction_eq_sum`: applying an arbitrary `k`-linear
functional `A -> k` to every coordinate of the acted-on vector is a linear
combination of the bounded ordered coefficient images. The scalar
coefficient at `a` is that functional applied to the monomial `t^a`.

`IsStableAtNilpotentTuples N W` requires all these scalar contractions to
belong to `W` whenever `v` belongs to `W`. This is equivalent to invariance
under every ordered coefficient product with exponent `a <= N`. Similarly,
`nilpotentOrbitSpan N v`, the span of all such contractions of actual
bounded-parameter actions on `v`, equals the span of the bounded ordered
divided-power images.

`IsFixedAtNilpotentTuples N v` requires the original scalar-extended vector
to be fixed at every such tuple. It holds exactly when the bounded ordered
coefficient image is `v` at exponent zero and is zero at every other
exponent. In one direction the universal quotient's coefficient
functionals extract these equations. In the other direction each orbit
coordinate minus the corresponding constant lies in `boxIdeal N`, so it
vanishes at every tuple with the specified power relations.

No infinitude or characteristic hypothesis is needed. The supplied field
and all commutative test algebras have universe `u`; the representation
index type is finite. These statements concern the specified ordered
family. The unit does not construct root coordinates, a Frobenius-kernel
group scheme, an entire induced-space comparison or Steinberg
irreducibility, and does not prove `SteinbergBigCellStatement`.
