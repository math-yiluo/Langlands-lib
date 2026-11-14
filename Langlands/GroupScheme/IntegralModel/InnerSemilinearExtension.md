# Integral extension of inner-twisted coefficient transport

This is an internal extension of the published `SemilinearExtension`
construction. All coefficient types have arbitrary common universe `u`.
Let `R` be a domain with fraction field `L`, let `k` be a field acting on
`L`, and let `P` be an integral model of the base change of a `k`-group `G`.
Fix a coefficient automorphism `σ` of `L` over `k` and an actual `L`-point
`z` of `G`. No cocycle hypothesis on `z` is needed for one automorphism.

`innerGaloisDescentIso` is the canonical generic coefficient comparison
followed by the actual group-scheme inner automorphism induced by `z`.
Its transport of a pulled-back integral section evaluates to
`z * rationalConjugate σ g * z⁻¹`, where `g` is the original generic value.
This follows by the published coefficient section-transport formula and
the all-test conjugation formula for `innerIso`.

Suppose the integral base map `a` is invertible, is compatible with `σ`
through the specified commuting square, and the explicit fixed-ring
property `HasSmoothHomExtension` holds. For a smooth `P`, assume both
`g ↦ z * rationalConjugate σ g * z⁻¹` and its inverse
`g ↦ rationalConjugate σ.symm (z⁻¹ * g * z)` preserve `P.integralPoints`.
`innerGaloisTwistIso` then constructs a compatible isomorphism from the
actual coefficient twist of `P` to `P`, with generic comparison
`innerGaloisDescentIso`.

The proof applies `isoOfSectionTransport`. Pullback of sections along
`a` is surjective. The transport formula gives the forward generic map,
and coefficient inversion followed by cancellation of conjugation gives
its inverse. The supplied extension property extends both generic
isomorphisms; the published generic rigidity proves that the extensions
are inverse.

`innerGaloisTwistIso_integralPointMap` records the exact generic evaluation
of the resulting transport of integral sections.
`innerGaloisTwistIso_generic_comm` records the full generic semilinear
compatibility square by the published `Hom.twist_generic_comm`.

The construction does not assert model existence, the extension property,
coherence for a family of coefficient automorphisms, effective descent,
or any reductive quotient or chamber assertion.
