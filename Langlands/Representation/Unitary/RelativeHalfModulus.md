# Smooth positive relative half modulus

Author: Worker 142.

This helper constructs the positive smooth square root needed in Renard 2026,
IV.2.1, (IV.2.1.1), printed p.97 / PDF p.103. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The auxiliary constructions are internal, derived from the published relative
modular character and the published positive-character square-root maps.

`positiveHalfSmoothCharacter` embeds the canonical nonnegative-real square root
of a positive unit-valued character into the complex units. Its kernel equals
the original kernel, hence it is smooth when the original character is smooth.
`positiveHalfSmoothCharacter_spec` proves strict positivity and the square
identity.

For a subgroup `H` of a locally compact nonarchimedean group `G`, with `H`
locally compact, `relativePositiveModulus H` is the unit-valued positive-real
character `Δ_H / (Δ_G|H)`, using Mathlib's modular convention.
`complexCharacter_relativePositiveModulus` identifies its complex embedding
with the unchanged published relative modular character.
`isOpen_ker_relativePositiveModulus` transports the open kernel of that
published smooth character. Finally, `exists_relativeHalfModulus` supplies a
smooth complex character with positive real values whose square is exactly
the published relative character. Closedness and quotient compactness are
unnecessary for this construction.
