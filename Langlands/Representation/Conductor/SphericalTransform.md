# The Laurent-valued corank-one integrand

This internal construction supplies the Laurent-valued integrand on the actual
left upper-unipotent quotient used by the corrected essential-vector argument.
It combines the existing polynomial-valued spherical formula, its homogeneity,
and the published scalar corank-one integrand. It does not assert an essential
identity or any conductor conclusion.

`symmetricTorusHomogeneousSubmodule σ K d` is the submodule of the existing
symmetric Laurent algebra whose elements scale by the scalar `c^d` under
simultaneous coordinate scaling by every unit `c`. The finite coordinate type,
field and integral degree are arbitrary. Additivity of scaling and its
coefficient-fixing algebra-map law prove closure under addition and scalar
multiplication.

Let `F` be a topological valued field with a chosen uniformizing element,
`ψ` a unitary additive character, and `W` a Whittaker function on
`GL_(n+2)(F)`. The value of `corankOnePolynomialFunction` at `g` in
`GL_(n+1)(F)` is the polynomial spherical function for the inverse standard
character, multiplied by the complex scalar

`W(diag(g,1)) * determinantWeight abv g (0 - 1/2)`.

Here `abv` and the natural parameter `q` remain explicit. The determinant
factor is exactly the factor occurring in the scalar corank-one integral at
spectral value zero.

Assume that `ψ` is trivial on the valuation integer ring. Evaluation at every
complex unit tuple gives the published `corankOneFunction` for the explicit
`inverseSphericalWhittaker`, at spectral value zero. The proof uses the
polynomial spherical specialization identity and commutativity of complex
multiplication. The scalar integrand is invariant under left multiplication by
the upper unipotent subgroup. Evaluation separation in the Laurent algebra
therefore proves the same invariance for the polynomial function.
`corankOnePolynomialIntegrand` descends this invariant function to the actual
`LeftUnipotentQuotient n F`; its evaluation is the published scalar
`corankOneIntegrand`, with the same hypotheses.

`sphericalQuotientDegree` is the sum of the chosen Iwasawa exponents.
The proved invariance of these exponents under left upper-unipotent
multiplication makes this an integer-valued function on the same quotient.
This definition needs no field topology.

The spherical homogeneity theorem and closure under scalar multiplication
show that the polynomial integrand at each quotient point is homogeneous of
that point's degree. `degreeCorankOnePolynomialIntegrand` keeps the value when
this degree equals the specified integer `d` and is zero otherwise.
It is homogeneous of degree `d` everywhere. Its scalar evaluation is the
similarly degree-restricted actual scalar integrand.

The provenance is internal: these are descent and submodule adapters for the
published concrete definitions and their proved identities. No principal-series
realization is assumed. This unit does not construct the coefficient integral,
prove integrability or compact support on degree strata, or identify the degree
with a normalized determinant norm. Those analytic and representation-theoretic
steps remain separate.
