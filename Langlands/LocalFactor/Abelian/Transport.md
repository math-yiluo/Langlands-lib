# Abelian epsilon expressions under field transport

This module constructs transport of the actual regular additive Haar measure
under an algebra equivalence of finite extensions of the same `Q_p`, and proves
compatibility of the existing measure-dependent abelian epsilon expression.
The fields may lie in independent universes. Both use their canonical
topological data, and the equivalence is over `Padic p`.

The namespace is `Langlands.PadicField.AbelianTransport`. Given
`e : F.Carrier ≃ₐ[Padic p] E.Carrier`, the characters are the existing inverse
pullbacks from `ConductorTransport`:

```
χ_E(u) = χ_F(e⁻¹(u)),
ψ_E(y) = ψ_F(e⁻¹(y)).
```

On units, the inverse map is the continuous units equivalence induced by `e`.
The additive character retains its continuity, nontriviality and unitary
codomain; the quasicharacter remains an arbitrary continuous complex
quasicharacter.

## Measure construction and domains of integration

`haarMeasure F E e μ` specializes
[`FieldTransport.haarMeasure`](../../HarmonicAnalysis/FieldTransport.md)
to `e.toRingEquiv`. The published canonical isometry supplies continuity in
both directions. Its underlying measure is exactly `Measure.map e μ.measure`,
and the imported constructor proves additive Haar invariance and regularity.
No normalization of the given Haar measure is required.

`setIntegral_haarMeasure` is change of variables for every complex-valued
function and every set, using the measurable embedding of the actual
homeomorphism. It compares integration over `s` against the pushforward with
integration over `e ⁻¹' s` against the original measure. This general identity
uses Mathlib's total Bochner integral convention. Its use below is on the
epsilon integrands already proved integrable in `Abelian.Definitions`.

`preimage_integers` identifies the preimage of the actual integer ring of `E`
with that of `F`, using preservation of the canonical discrete valuation.
Applying the measurable-embedding measure formula and then `ENNReal.toReal`
gives `integerVolume_eq`. The imported integer-volume construction is finite.
There is no extra Jacobian factor, since the measure itself is pushed forward.

`preimage_valuationShell` preserves every integer-indexed shell
`{x | discreteValuation x = WithZero.exp k}`. With the existing additive and
multiplicative conductor equalities, `preimage_epsilonShell` identifies the
shell at index `n(ψ)+a(χ)` in both fields. The sign is unchanged: a shell at
index `k` consists of elements of order `-k`.

## Actual integrands and both epsilon branches

`extendZero_map` compares the zero extensions of the transported
quasicharacters on every field element, including zero. At a nonzero element
the proof identifies the units produced by `Units.mk0` using the inverse
units map. `epsilonIntegrand_map` then preserves the existing plus-sign
integrand `χ(x)⁻¹ ψ(x)`.

`abelianGaussIntegral_eq` applies the set-integral change of variables, the
epsilon-shell preimage equality and this pointwise integrand equality.
Both integrals are the actual convergent Gauss integrals:
[`Abelian.Definitions`](Definitions.md) proves integrability on the compact
shell. The comparison does not assert nonvanishing or a functional equation.

The principal compatibility theorem is `abelianEpsilonExpression_eq`:

```
ε_E(χ_E, ψ_E, e_*μ) = ε_F(χ_F, ψ_F, μ).
```

The proof splits on the existing predicate that `χ_F` is unramified, and uses
the preservation and reflection of that predicate.

* In the ramified branch, the expression is the Gauss integral just compared.
* In the unramified branch, let `c` be the source's existing `abelianScale`
  at index `n(ψ_F)`. Its image under the units equivalence has the required
  target valuation because both valuation and additive conductor are
  preserved. The target's published
  `abelianEpsilonExpression_unramified_scale` therefore computes its value
  using this image. Inverse pullback preserves `χ(c)`, canonical transport
  preserves `|c|`, and `integerVolume_eq` preserves the remaining integer-ring
  volume. These are precisely the three quantities in
  `χ(c) / |c| · vol_μ(O)`.

The proof does not identify the independently chosen source and target scales
or uniformizers. It uses the already proved independence of the allowed scale.

## Provenance and scope

This is an internal compatibility construction of existing Library objects.
The direct imports are
[`ConductorTransport`](../../HarmonicAnalysis/ConductorTransport.md) and
[`Abelian.Definitions`](Definitions.md). They supply actual character
transport, preserved conductors and unramifiedness, the convergent Gauss
integral, and the two epsilon formulas with scale independence.
`CanonicalTransport` supplies valuation and normalized-absolute-value
preservation; `FieldTransport` supplies pushforward Haar regularity.
The implementation specializes Mathlib's measurable-embedding change of
variables and proves the needed preimage identities. It introduces no new
external-source claim. The original epsilon conventions and source references
remain those documented in `Abelian.Definitions`.

The comparison is for an invertible algebra map of finite `p`-adic fields,
with the measure and both characters transported by that same map. It is for
the existing complex-valued constant; no spectral twist or half shift is
inserted. Spectral and rational abelian factor transport are separate
constructions. This module does not assume reciprocity, choose a self-dual
measure, supply an epsilon-system existence theorem, or construct an
unconditional nonabelian epsilon factor.
