# Canonical character-change quotient Haar measure law

Worker 88 states the canonical local-field instance of the published
`Langlands.RankinSelberg.HasCharacterChangeMeasureLaw`. This is an internal
statement assembled from the Library's actual constructions, not a
transcription of a new literature theorem. Its provenance is
`RankinSelberg/CharacterChange` (the map, exponent, modulus and measure-law
predicate), `RankinSelberg/AnalyticStatement` (the normalized absolute value),
`RankinSelberg/Measures` (the actual Haar measures),
`RankinSelberg/UnipotentUnimodularity` (the right-invariance instance), and
`Analysis/Local/QuotientMeasure` (compatibility and the Weil convention).
`LocalField/Normalization/Proof` supplies the normalization used by
`normalizedAbsoluteValue`.

## Exact scope

`CharacterChangeCompatibleMeasureStatement.{uF}` is a closed proposition
definition at the field-carrier universe `uF`. It quantifies over every prime
natural number `p` with its `Fact p.Prime` instance, every `PadicField p`,
every actual `F.TopologicalData` value `T`, every natural `n`, every unit
`a : F.Carrierˣ`, and every compatible quotient measure `μ`.
The matrix rank is `n + 1`, including rank one when `n = 0`.

The definition installs `T.topology`, `T.valuativeRel` and `T.localField`.
It explicitly installs the Borel measurable structures on the general linear
group, its upper-unipotent subgroup and the left quotient, all formed from
that topology. There is no unrelated topology or free measurable structure.

Compatibility is exactly the existing
`QuotientIntegration.IsCompatible` for `generalLinearHaar F.Carrier n`
and `unipotentHaar F.Carrier n`. These are the measures normalized to give
the integral general linear and integral unipotent subgroups mass one.
The compatibility predicate requires a nonzero regular quotient measure,
right-translation invariance, integrability of compact continuous orbital
averages, and the complex Weil integration identity. Its prerequisite
`Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)` is synthesized
from the imported, proved `unipotentHaar_isMulRightInvariant` instance;
it is not a quantified hypothesis.

The conclusion unfolds to

```text
Measure.map (characterChangeQuotient a n) μ
  = (characterChangeModulus (normalizedAbsoluteValue T) a n : ℝ≥0∞) • μ.
```

Here the actual homeomorphism sends `N g` to `N d_a g`, where
`d_a = diag(a^n, a^(n-1), ..., 1)`, on the existing left quotient
`N_(n+1) \ GL_(n+1)(F)`. Its multiplier is
`c = |a|^E`, with `E = sum_{0 ≤ i < j < n+1} (j-i)` exactly as defined
by `characterChangeRootExponent`; it is not the inverse multiplier.
The absolute value is `normalizedAbsoluteValue T`, so a uniformizer has
absolute value `T.residueCardinality⁻¹`. In rank one the exponent is zero
and the diagonal is the identity.

## Why this sign follows from the Weil convention

Write `νG` and `νN` for the two actual Haar measures and
`A f(N g) = ∫_N f(u g) dνN(u)` for the published averaging convention.
Compatibility gives

```text
∫ A f(q) dμ(q) = ∫ f(g) dνG(g)
```

for compactly supported continuous complex `f`. Conjugation
`C_a(u) = d_a u d_a⁻¹` multiplies the `(i,j)` coordinate by `a^(j-i)`.
The resulting expected conjugation Jacobian is the separate measure
identity `(C_a)_*νN = c⁻¹ νN`: pushforward along coordinate dilation
uses the reciprocal of its volume factor. Establishing this identity
for the actual normalized unipotent Haar measure is a proof obligation,
not an assumption of the Lean target.

Given that conjugation identity, substitution in the orbital integral
determines the direction of the quotient multiplier:

```text
A(f ∘ L_d_a)(N g)
  = ∫ f(C_a(u) d_a g) dνN(u)
  = c⁻¹ A f(N d_a g).
```

Left invariance of `νG` and compatibility applied to `f ∘ L_d_a` therefore
give

```text
c⁻¹ ∫ A f(T_a q) dμ(q) = ∫ f(g) dνG(g) = ∫ A f(q) dμ(q),
```

where `T_a = characterChangeQuotient a n`. Since `c` is positive and
finite, this yields the factor `c` for the quotient pushforward. Passing
from orbital averages to equality of measures requires the corresponding
lifting and measure-uniqueness argument. The Library's
`RankinSelberg/UnipotentQuotient` already proves existence and uniqueness
of the compatible measure, through `unipotentQuotientHaar_isCompatible`
and `unipotentQuotientHaar_unique`; these can be reused in a later proof.
They also show the target's compatible-measure quantifier has actual
instances. No uniqueness statement is assumed here.

This sign calculation explains the proposed statement. This module contains
no proof of the conjugation Jacobian, the quotient measure identity, or
their analytic consequences. It adds only the proposition definition,
without changing any normalization, quotient or compatibility definition.
