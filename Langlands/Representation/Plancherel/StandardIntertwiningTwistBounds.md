# A common growth exponent for character-twisted scalar convergence

This internal construction applies the actual scalar Iwasawa convergence
reduction to open-kernel character twists of one fixed smooth inducing
representation. The ambient group and representation carrier retain independent
universes, and the carrier has no norm or topology.

The published `smoothContragredientTwistEquiv` sends a smooth functional for
the twisted action to the same underlying linear functional for the original
action. Evaluating the actual twisted action and using linearity therefore
multiplies the coefficient norm by `‖χ(m)‖`. Consequently, a coefficient
envelope `ξ` for the original representation gives the envelope
`m ↦ ‖χ(m)‖ * ξ(m)` for its twist. Its positive constant may depend on the
vector and the transferred functional.

`twistIwasawaWeight` is the existing actual source half-character norm
multiplied by `‖χ(m)‖ * H(m)^d`, where `m` is the Levi projection of the
supplied parabolic coordinate of an actual quotient point. The coordinates
have exactly the representative factorization required by
`scalarDomain_eq_top_of_integrable_iwasawaWeight`; no measurable section or
integrability property is asserted merely by choosing them.

The main result starts with one exponent `d` for all coefficients of the
original representation. It chooses this exponent before quantifying over
the varying character and its open-kernel proof. For every such character,
integrability of the explicitly twisted weight implies that the scalar
domain is the whole actual induced source. The proof transfers the original
coefficient bound using the smooth-dual equivalence and applies the preceding
scalar domination theorem. The height lower bound ensures that its power
envelope is nonnegative.

The provenance is internal, using the actual twist definition, the published
functional-preserving smooth-dual equivalence, and the scalar Iwasawa
reduction. The result assumes the displayed common growth exponent and
geometric weight integrability; it proves neither of them. In particular,
it supplies no root-cone threshold, rational continuation, denominator
regularity, or new final premise for the unchanged conditional intertwining
theorem.
