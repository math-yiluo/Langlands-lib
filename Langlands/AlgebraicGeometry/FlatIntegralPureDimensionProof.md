# Componentwise pure dimension for flat integral extensions

This is an internal proof of the exact proposition
`Langlands.AlgebraicGeometry.SchemeFiberGeometry.FlatIntegralPureRingDimensionInvariance`.
The target and its import closure are unchanged. Worker 105 developed the
Lean proof; Worker 1341 prepared this contribution from the shared draft.
The result is an internal algebraic prerequisite for the field-extension
argument described in the statement's Markdown, rather than a separate
assertion from the motivating literature.

`under_mem_minimalPrimes_of_flat` applies Mathlib going down for flat algebras.
Given a prime below the contraction of a minimal prime q, going down produces
a prime Q below q lying over it. Minimality forces Q = q, so contraction is
minimal. No Noetherian hypothesis is used.

`ringKrullDim_quotient_under_eq_of_integral` uses the actual induced map
R/(q ∩ R) → S/q. Mathlib proves that it is injective and integral. The existing
published integral-extension dimension theorem in
`P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen`
then identifies the two quotient-ring dimensions. This lemma even holds for
arbitrary ideals q. The reused theorem
`ringKrullDim_eq_of_ringHom_isIntegral_of_injective` assumes only
commutative rings and an integral injective ring homomorphism; its ambient
module's curve-theoretic results add no hypotheses to this application.

The main theorem transports dimensions of all minimal-prime quotients along
these two results in the forward direction. In the reverse direction,
injectivity and Mathlib's minimal-prime lifting theorem give a minimal q
above each minimal p. The same quotient-dimension equality transports the
common dimension back. This proves the exact universal proposition in two
independent universes, for every natural d and arbitrary commutative rings,
including zero rings. Flatness, integrality and `FaithfulSMul R S` are the
only assumptions on the algebra extension. No Noetherian, finite-type or
field hypothesis is introduced.

Arbitrary-field-extension invariance and filtered-fibre descent remain
separate obligations of parent task
`886bf565-95e9-4dc6-8a9d-73284a523668`, revision 1.
