# Parameter continuity of actual compact standard integrals

This derived supporting construction uses the published actual compact sections,
normalized covariance extension and standard integral. Its scalar integral
continuity follows from Mathlib dominated convergence. It does not assume a
norm or topology on the algebraic inducing carrier, and does not assert
convergence or the locally uniform domination estimate needed in its application.

## Scope and fixed-point regularity

The ambient nonarchimedean locally compact group, source semidirect
decomposition, closed source radical, unimodular-modulus compatibility,
compact open subgroup and source Iwasawa factorization are explicit. The
actual unramified character space belongs to the supplied continuous family
of positive unit-valued homomorphisms on the Levi, with continuous Levi
projection. The inducing smooth complex representation has an independent
carrier universe. No admissibility or finite-length premise is needed here.

`unramifiedCompactExtension_eval_factor` writes the extension of a fixed
compact section at a fixed ambient point as one actual character evaluation
times a fixed vector. Factor the ambient point as an inducing-subgroup point
followed by a compact-subgroup point. The normalized covariance formula
places the half-modulus and original Levi action in the fixed vector. The
remaining factor is the character evaluated at the Levi projection of the
inducing-subgroup point. Scalar commutation gives the stated order.

`unramifiedCompactExtension_eval_isPolynomialOn` uses that factorization
with a singleton finite expansion, proving polynomial vector dependence on
every parameter subset in the existing `IsPolynomialOn` predicate.
`continuous_unramifiedCompactExtension_scalar` applies any algebraic linear
functional to the same factorization. Character evaluation is continuous in
the full compact-open character topology, and the remaining scalar is fixed.

`unramifiedCompactIntegrand` is the existing descended quotient integrand
of the compact section extended at each actual character. The quotient is the
actual left quotient of the target radical by the source/target intersection;
the intersection need not be normal. `continuous_unramifiedCompactIntegrand_scalar`
uses quotient induction to reduce scalar parameter continuity at each quotient
point to the fixed-point extension result.

## Scalar integrals and the compact operator

For any measure on that quotient,
`unramifiedCompactIntegrand_scalar_integrable` assumes that the original
standard integral domain equals the whole source at the specified character.
It proves integrability against each fixed smooth functional of the original
untwisted representation. The published `smoothContragredientTwistEquiv`
transports that functional to the smooth dual of the twist while preserving
its underlying linear functional. The full-domain equality puts the extended
section in the actual domain, and its defining weak-integral relation supplies
scalar integrability. The representation carrier is unchanged by twisting.

`continuousAt_unramifiedCompactScalarIntegral_of_dominated` allows any
first-countable topological parameter space and a map into actual unramified
characters which is continuous at the specified point. It takes eventual
almost-everywhere strong measurability and an eventual almost-everywhere norm
bound by one integrable real function on the quotient. It concludes continuity
at that point of the genuine complex scalar integral, for any fixed algebraic
linear functional. Pointwise scalar continuity, composed with the parameter
map, supplies the continuity premise of Mathlib
`MeasureTheory.continuousAt_of_dominated`.

`standardCompactOperator_scalar_eval` also takes the published target-side
closedness, modulus, Iwasawa and projection data, fixed regular two-sided Haar
measures with a compatible quotient measure, closed Levi, squared-modulus
compatibility and the full-domain equality. For a fixed compact input, compact
evaluation point and smooth functional of the original representation, it
identifies the scalar test of the actual compact standard operator with the
genuine scalar integral of `unramifiedCompactIntegrand`. The proof transports
the smooth functional through the same twist equivalence and applies the
published `operator_eval`; the compact restriction and source inclusion retain
the underlying functions.

`continuousAt_standardCompactOperator_scalar_of_dominated` uses a
first-countable parameter space, a parameter map continuous at the chosen
point, and full-domain equality at each parameter in that space. With an
eventual almost-everywhere norm bound by a fixed integrable real function,
it proves continuity of the scalar test of the actual compact standard
operator. Scalar integrability gives the required strong measurability at
each parameter. The scalar evaluation identity and the preceding dominated
integral theorem finish the proof. A parameter space may in particular be a
subset of the character space or a coordinate space, provided its displayed
topological hypotheses hold; no first-countability claim for arbitrary
character spaces is made here.

## Provenance and retained obligations

The results are derived from the published covariance, actual-domain and
scalar-integral identities, twist preservation of smooth duals, continuity of
character evaluation and Mathlib's dominated-convergence continuity theorem.
They do not transcribe an external representation-theoretic theorem and need
no new literature premise.

The local integrable domination estimate remains an explicit hypothesis; no
such estimate, convergence on a cone, holomorphy, denominator cancellation,
rationality of the integral or the host conditional standard intertwining
theorem is proved by this unit. Pointwise polynomiality of the integrand does
not assert polynomiality of its integral. All actual modulus and full-domain
prerequisites of the compact operator remain explicit.
