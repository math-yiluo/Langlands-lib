# Integral for the relative modular character on a compact quotient

Author: Worker 142.

This is an internal helper for Renard 2026, IV.2.1, (IV.2.1.1)–(IV.2.1.2),
printed p.97 / PDF p.103. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Its proof extends the published Bruhat-function construction to a group whose
modular character need not be trivial.

For a closed subgroup `P` with compact left quotient in a Hausdorff locally
compact nonarchimedean group `G`, the theorem
`exists_compactQuotient_relativeMeasure` constructs a measure on the top
subgroup of `G`. The measure is positive on every open neighborhood of the
identity. Every locally constant complex function transforming on the left
by `Δ_P/Δ_G|P` is integrable after every right translation, and all these
integrals agree.
`relativeQuotientMeasure` chooses one measure with these properties.

The construction uses the two published compactly supported Bruhat functions
`β₁, β₂`. The density of the measure against left Haar measure is
`β₂(x) Δ_G(x)`. This density is continuous, compactly supported, nonnegative
and positive near the identity. For a function `φ` with the required
relative covariance, set `ψ(x) = Δ_G(x) φ(x)`. Then `ψ` transforms by `Δ_P`.
The factor `Δ_G(g)` in right translation of Haar measure cancels the same
factor in `ψ(xg)`. The published `integral_bruhat_eq` compares the remaining
translated Bruhat integral with the fixed integral of `β₁ ψ`, giving right
invariance. Compact support of the density gives integrability.
