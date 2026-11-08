# Local constancy and integrability of Laurent quotient coefficients

This internal unit supplies analytic adapters for the actual Laurent-valued
corank-one integrand. It proves local constancy and derives scalar
integrability from compact support. Compact support for degree restrictions of
actual model vectors remains a separate obligation, as do convergence of the
full integral, rational continuation, the essential identity and the conductor
conclusions.

## Scalar integrability without a coefficient topology

Let `X` be a topological measurable space whose open sets are measurable, let
`μ` be finite on compact sets, and let `A` be a complex module with an additive
group structure. For a locally constant, compactly supported function
`f : X → A`,
`isScalarIntegrable_coefficientSpanFunction_of_locallyConstant` proves scalar
integrability of `coefficientSpanFunction f` in its actual complex range span.
No topology on `A`, or finite-dimensionality hypothesis, is required.

The proof first descends local constancy through the injective inclusion of the
range span. Its support is contained in the support of `f`. Every algebraic
linear form on that span therefore gives a locally constant, compactly
supported complex function. This function is continuous and integrable by
Mathlib's compact-support integration theorem. This is exactly the definition
of `IsScalarIntegrable`.

## Local constancy on the actual quotient

Here `F` is any nonarchimedean local field, `ϖ` is a uniformizing unit, and the
lower group is `GL_(n+1)(F)`. The quotient is the existing left quotient by its
upper unipotent subgroup. The private invariant-function lemma proves local
constancy from right invariance under `GL_(n+1)(O)`, using the open level-zero
subgroup. The private quotient lemma uses the existing open quotient map to
descend local constancy.

`determinantWeight_isLocallyConstant` assumes that the supplied absolute value
`abv` is one on valuation units. The determinant weight is right integral
invariant, so it is locally constant for every complex spectral parameter.
`sphericalQuotientDegree_isLocallyConstant` uses right integral invariance of
the actual Iwasawa exponent tuple, then descends the sum to the quotient.

For an integrally trivial unitary additive character `ψ`, a natural number
`q`, and `W : WhittakerFunctions ψ (n+1)`, assume `W.val` is locally constant.
`corankOnePolynomialFunction_isLocallyConstant` composes `W` with
`diag(g,1)`, multiplies by the determinant weight at `-1/2`, and applies scalar
multiplication to the locally constant inverse-character spherical Laurent
polynomial. `corankOnePolynomialIntegrand_isLocallyConstant` descends this
property. `degreeCorankOnePolynomialIntegrand_isLocallyConstant` combines it
with the locally constant degree, retaining the original value on the degree
`d` locus and zero elsewhere.

If the quotient has measurable open sets and `μ` is finite on compact sets,
`degreeCorankOnePolynomialIntegrand_isScalarIntegrable` consequently proves
scalar integrability in the actual value span whenever this degree integrand
has compact support. Neither residue-cardinality normalization nor a prescribed
quotient measure is needed for this intermediate result.

## Smooth model vectors and Jacquet normalization

`degreeCorankOneModelIntegrand h π ℓ w d` defines the actual degree-restricted
Laurent quotient integrand for a coefficient-model vector. It supplies the
uniformizer proof and the integral character triviality from the existing
Jacquet normalization `h`. Its value space is the symmetric Laurent algebra
on `Fin (n+1)` over `ℂ`. This definition needs no smoothness assumption on `π`.

`degreeCorankOnePolynomialIntegrand_model_isScalarIntegrable` specializes to
an actual model vector `w` of a smooth representation `π` on `GL_(n+2)(F)`
with a specified standard Whittaker functional `ℓ`. The field and representation
space have independent universes. Given the existing `IsJacquetNormalization`
data `h`, it derives local constancy from
`glModelFunction_isLocallyConstant`, installs the quotient Borel structure from
`h.borel`, and obtains finiteness on compact sets from `h.measure.regular`.
The absolute-value condition and integral triviality of `ψ` come from
`h.abv_unit` and `h.conductor.1`. Thus the only additional analytic premise of
this adapter is compact support of the actual degree-restricted Laurent
integrand just defined. Irreducibility, admissibility and nonzeroness of `ℓ` are unnecessary
for this implication.

## Provenance

All assertions are internal deductions from the existing actual quotient,
smooth coefficient model, integral invariance of the determinant weight,
spherical Laurent formula, coefficient range span, and Mathlib's
locally-constant and compact-support integration interfaces. No external
representation-theoretic or support theorem is asserted in this unit.
