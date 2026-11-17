# The graded subalgebra of invariant polynomials

This internal module constructs
`MatrixRepresentation.invariantPolynomialSubalgebra ρ` over any commutative
coefficient ring `R : CommRingCat.{u}`. Its elements are exactly the
polynomials satisfying the published `ρ.IsInvariantPolynomial` predicate:
evaluation is unchanged under the representation at every point over every
test scheme. Addition, multiplication, and inclusion of coefficients follow
directly because polynomial evaluation is a ring homomorphism.

Homogeneous components commute both with change of coefficients
(`map_homogeneousComponent`) and with linear substitution
(`linearPullback_homogeneousComponent`). The first assertion is checked on
coefficients. The second follows by induction on polynomials: a monomial is
homogeneous, linear substitution preserves its degree, and both operations
are additive. Consequently `actionPolynomial_homogeneousComponent` shows
that the polynomial action commutes with taking homogeneous components.

When the acting group scheme is affine,
`IsInvariantPolynomial.homogeneousComponent` takes a homogeneous component
of the universal polynomial identity. The published universal-identity
criterion then gives invariance over every test scheme. This proof uses
polynomial identities, with no density or reducedness assumption.
`polynomial_proj_eq_homogeneousComponent` identifies the homogeneous
component with the standard graded-ring projection, and
`invariantPolynomialSubalgebra_proj_mem` gives closure of the invariant
subalgebra under those projections.

Finally `invariantPolynomialSubalgebra_fg_iff` identifies algebra finite
generation (`Subalgebra.FG`) with the explicit finite set of invariant
generators and algebra-adjoin condition in
`LinearlyReductiveInvariantFiniteGenerationStatement`. This equivalence
needs no affineness, field, or reductivity hypothesis.

Provenance is derived internal content: these are elementary algebra
consequences of the published invariant-polynomial predicate, the universal
polynomial identity and linear-pullback homogeneity, together with Mathlib's
homogeneous polynomial decomposition and definition of finite generation.
No new invariant-theory existence theorem is asserted. In particular, this
module neither constructs a Reynolds operator nor proves that the invariant
subalgebra is finitely generated.
