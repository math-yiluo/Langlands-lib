# Rational and spectral abelian factors under field transport

This module constructs the equivalence between the actual regular spectral
domains of a quasicharacter and its transport, and proves compatibility of the
existing rational L-factor and spectral epsilon expressions. It is an internal
compatibility construction using the published
[abelian spectral expressions](Padic.md),
[Haar and epsilon transport](Transport.md),
[conductor transport](../../HarmonicAnalysis/ConductorTransport.md), and
[canonical arithmetic transport](../../LocalField/CanonicalTransport.md).
Worker 20 authored this module.

## Inputs and conventions

The namespace is `Langlands.PadicField.AbelianTransport`. The inputs are finite
p-adic fields `F` and `E`, in independent universes, for the same prime `p`, and
an actual algebra equivalence `e : F.Carrier ≃ₐ[Padic p] E.Carrier`. Both fields
use their canonical topological data and the corresponding Borel measurable
spaces.

Write `chi_E` and `psi_E` for the published inverse-pullback transports
`ConductorTransport.quasicharacter F E e chi` and
`ConductorTransport.additiveCharacter F E e psi`. Here `chi` is any continuous
complex-unit-valued quasicharacter, and `psi` is a continuous nontrivial
unitary additive character. For a supplied regular additive Haar measure
`mu`, write `mu_E` for `AbelianTransport.haarMeasure F E e mu`. Its underlying
measure is `Measure.map e mu.measure`. These are actual transports by the
same field map.

The source and target uniformizers are independently chosen by their canonical
topological data. `uniformizer_value_eq` proves
`chi_E(pi_E) = chi(pi_F)` when `chi` is unramified. The proof first transports
unramifiedness, then observes that `pi_E` and the image of `pi_F` have the same
discrete valuation. The existing theorem that an unramified character has
equal values on elements of equal valuation compares them. Inverse cancellation
identifies the latter value with `chi(pi_F)`. No equality between the chosen
uniformizers is asserted.

## Rational factors and the regular domain

Let `a` be the actual multiplicative conductor and `q` the actual residue
cardinality. The existing Euler polynomial is

```text
P_chi(X) = 1 - chi(pi) X  if a = 0,
           1             otherwise.
```

Its constant term is one, as proved in `Padic`. The spectral coordinate is
`z(s) = exp(-s log q)`. `spectralVariable_eq` uses the intrinsic residue-cardinality
equality to prove that this coordinate agrees over the two fields for the same
complex `s`. `lPolynomial_eq` combines the preserved conductor with
`uniformizer_value_eq` in the unramified case. The ramified polynomials are
both one. `rationalLFactor_eq` then identifies their reciprocals in
`RatFunc ℂ`.

`regularPoint_iff` proves equivalence of the existing predicates at each `s`,
with each field's own conductor and chosen uniformizer. It rewrites them as
`P_chi(z(s)) ≠ 0`, using `regularPoint_iff_polynomial_ne_zero`, and applies
the polynomial and spectral-variable equalities.

The definition `regularPointEquiv` is an equivalence between those two actual
subtypes of `ℂ`. Both its forward and inverse maps retain the complex
coordinate and transport only its proof of regularity. Its inverse laws are
reflexive, and `regularPointEquiv_val` records the unchanged coordinate.
`regularLValue_eq` proves equality in `ℂˣ` of the existing reciprocal
evaluations at the corresponding points. The proof reduces equality of units
to equality of their complex values and rewrites the polynomial and variable.
Thus the rational factors retain their poles, and the numerical comparison
uses exactly their regular domains.

## Spectral epsilon and the two constants

For every complex `s`, `gaussIntegrand_map` identifies the actual spectral
integrand at `e x` with the source integrand at `x`:

```text
chi(x)^(-1) * exp(-s log |x|) * psi(x).
```

Here the quasicharacter is extended by zero at the origin, as in `Padic`.
The proof uses the existing zero-extension transport identity, preservation
of the normalized absolute value, and inverse cancellation for the additive
character. The Fourier sign remains positive.

`preimage_gaussShell` identifies the preimage of the target annulus
`{x | x ≠ 0 and ord(x) = -d}` with the source annulus at the same integer
`d`. It uses the published identification with valuation shells and their
transport identity.

`epsilon_eq` states, for all `s`,

```text
epsilon_E(chi_E, psi_E, mu_E, s) = epsilon_F(chi, psi, mu, s).
```

The proof rewrites both actual conductor indices and separates the two
branches of the existing definition. When the multiplicative conductor is
zero, the expression is

```text
chi(pi)^n * exp(n * (1 - s) * log q) * vol_mu(O),
```

where `n` is the additive conductor. The preceding uniformizer-value
comparison, residue-cardinality preservation and published integer-ring
volume comparison identify its factors. Otherwise, the expression is the
set integral of the spectral Gauss integrand over the shell at `n + a`.
The published pushforward set-integral formula, shell preimage equality and
pointwise integrand identity identify the two integrals. The imported
`gaussIntegrand_integrable` theorem proves convergence on every such shell
for every complex parameter and every regular additive Haar measure.

`deligneConstant_eq` specializes this equality to `s = 0`, retaining the
supplied Haar measure and its pushforward. `centeredConstant_eq` specializes
it to `s = 1/2`, with the same measures. These are the existing unshifted and
centered conventions from `Padic`. The module selects no self-dual measure
and makes no self-dual-normalization or nonvanishing claim.

## Provenance and scope

All new declarations are derived from the imported constructions. The
polynomial, rational factor, spectral expressions, convergence theorem and
normalization conventions are those of `Langlands.LocalFactor.Abelian.Padic`;
their original-source documentation remains in its paired Markdown. The
transport input maps, conductor equalities, arithmetic invariants and
set-integral formula are proved in the published dependency modules named
above. This module adds no external-source assertion or assumed invariance
law.

The result concerns canonical field presentations related by an invertible
algebra map and transports the characters and the supplied measure together.
It establishes construction compatibility, with the regular domain explicit.
It does not assert a functional equation, nonabelian constant-system
existence, or a choice of self-dual Haar measure.
