# Degree coefficients of the Laurent quotient integrand

This internal adapter constructs one Laurent coefficient from the existing
degree-restricted corank-one integrand on the actual left upper-unipotent
quotient. It proves finite-dimensionality from compact quotient support,
preservation of the integral degree, and scalar evaluation under explicit
integrability. It leaves the analytic support and integrability of actual model
vectors to subsequent results.

The field has its own universe and is a topological valued field with a chosen
uniformizing element. The unitary additive character `ψ` is trivial on the
valuation integer ring. The Whittaker function `W`, absolute value `abv`,
natural parameter `q` and integer degree `d` remain explicit. The definition
`degreeCorankOnePolynomialSpan` is the complex span of the range of
`degreeCorankOnePolynomialIntegrand`, in the existing symmetric Laurent algebra.

Over a nonarchimedean local field, suppose a compact subset `D` of the actual
left quotient contains the support of this degree-restricted integrand.
`degreeCorankOnePolynomialSpan_finite_of_compactSupport` proves that its actual
value span is finite-dimensional. The proof applies the existing compact-modulo-
unipotent spherical finiteness theorem to the inverse standard character.
That theorem supplies a single finite-dimensional submodule containing every
spherical value at representatives above `D`. The polynomial corank-one
integrand is a scalar multiple of the corresponding spherical value, so also
belongs to this submodule above `D`; the degree restriction can only replace
that value by zero. Outside `D` the support hypothesis gives zero. The universal
property of the span and containment in a finite-dimensional submodule complete
the proof. In particular, finite-dimensionality is proved from the stated support
condition rather than assumed in this theorem.

Give the quotient any measurable-space structure and measure `μ`. When the
actual value span is finite-dimensional, `degreeCorankOneCoefficient` is
`finiteSpanCoefficientIntegral` of the degree-restricted Laurent integrand.
This integrates in the actual range-span subtype and includes the resulting
vector in the ambient symmetric Laurent algebra; no topology on that algebra
is chosen. The definition is total, as are its scalar Bochner coordinate
integrals.

Every integrand value is homogeneous of degree `d`. These values lie in the
homogeneous submodule constructed in `SphericalTransform`. The coefficient
integral's submodule-preservation theorem therefore proves
`degreeCorankOneCoefficient_isHomogeneous`, with no integrability hypothesis.

For the scalar evaluation identity, the hypotheses explicitly require
`IsScalarIntegrable μ (coefficientSpanFunction f)`, where `f` is the
degree-restricted integrand. Thus every algebraic complex linear functional on
its actual value span is integrable. Apply the coefficient integral's
linear-evaluation theorem to evaluation at a complex unit tuple, then use
the existing polynomial integrand specialization. The result is the integral
over the actual quotient of the scalar corank-one integrand at spectral value
zero when the quotient degree equals `d`, and zero otherwise.

The provenance is internal. This unit combines the proved compact spherical
finiteness, actual quotient descent and homogeneity, and finite-span
coefficient integration. It asserts neither compact support nor integrability
for arbitrary Whittaker-model vectors, chooses no Haar normalization, and
does not compare Iwasawa degree with determinant norm. Principal-series
realization, the Laurent series and denominator argument, essential-vector
existence and uniqueness, and conductor conclusions remain open.
