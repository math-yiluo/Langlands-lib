# Ambient unit certificates from quotient principal neighborhoods

`affinePrincipalPullbacks` is the set of pullbacks of actual quotient global sections whose principal opens are affine. If the ambient group scheme is affine and these quotient principal opens cover, their inverse images cover the ambient scheme. The affine-scheme criterion for principal covers therefore says that these pullbacks generate the unit ideal in the ambient coordinate ring.

Extracting a finite subset generating that ideal gives a finite family of quotient sections, each with affine principal open, together with ambient coefficients whose sum of products with the pulled-back sections equals one. The proof chooses a quotient section lifting each element of the finite subset, uses the finite span criterion for the coefficient expression, and enumerates the finite family by `Fin n`.

The final theorem supplies this data under explicit geometric reductivity for a smooth subgroup over an algebraically closed field, by applying the separately implemented principal-neighborhood construction to the same supplied quotient. All natural family sizes are allowed.

The coefficient certificate is an equality in the ambient section ring. Its coefficients need not be invariant. No unit-ideal conclusion in the quotient section ring, and no unconditional reductive quotient affineness theorem, is asserted here. Turning this certificate into an invariant-coefficient one remains a separate step.

Provenance: internal derived construction from the supplied quotient's affine principal cover and Mathlib's affine principal-open cover, finite ideal generation and finite linear combination criteria. No external source is transcribed.
