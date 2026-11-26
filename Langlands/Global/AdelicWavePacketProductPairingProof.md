# Factorization of the quotient-product pairing

Module `Langlands.Global.AdelicWavePacketProductPairingProof` proves
`Langlands.Global.WavePacketProductPairingStatement` (module
`Langlands.Global.AdelicWavePacketProductPairingStatement`) from
`Langlands.Global.RestrictionSplitCentre.PrincipalQuotientProductMeasureStatement` (module
`Langlands.Global.AdelicPrincipalQuotientProductMeasureStatement`), which it takes as a hypothesis
and does not prove.

| Declaration | Kind | Content |
| --- | --- | --- |
| `wavePacketProductPairing_of_productMeasure` | theorem (proved) | `PrincipalQuotientProductMeasureStatement → WavePacketProductPairingStatement` |

The remaining declarations of the module are private lemmas of this proof.

## Proof

Write `α = positiveCentreHaarMeasure F G hG`, `ν = canonicalMeasure F G`, `A = profile|_{A_G}` and
`E = principalQuotientProductEquiv F G hG`. The hypothesis says that `E` carries
`rationalQuotientHaarMeasure F G` to `α.prod ν`. `ambientWavePacketProfile_squareIntegrable`
(module `Langlands.Global.AdelicAmbientWavePacketProfileProof`) gives `A ∈ L²(α)` and, for
`b ≠ 0`, `c = ∫ ‖A‖² dα > 0`: clause 1.

Clause 2. Write `g = a · n` with `a ∈ A_G` and `n ∈ G(𝔸)¹` (`intrinsicNormOneDecomposition`).
Then `E[g] = (a, [n])` (`principalQuotientProductHomeomorph_mk`), the second coordinate of `E[g]`
is `[g]` (`principalQuotientProductHomeomorph_snd_mk`), and `H_G(g) = H_G(a)` because `H_G`
vanishes on `G(𝔸)¹` (`characterLog_eq_zero_iff`), so `profile(g) = profile(a)`.

Clause 3. Through the measure-preserving `E`, the lift is in `L²` exactly when
`(a, y) ↦ A(a) f(y)` is in `L²(α.prod ν)`. For an almost everywhere strongly measurable `f`,
Tonelli (`lintegral_prod_mul`) gives `∫⁻ ‖A(a) f(y)‖² = (∫⁻ ‖A‖²) (∫⁻ ‖f‖²)` with a finite nonzero
first factor, so the product is in `L²` exactly when `f` is. Conversely, if the product is in `L²`
it is almost everywhere strongly measurable, so almost every section `y ↦ A(a) f(y)` is
(`AEStronglyMeasurable.prodMk_left`); since `∫ ‖A‖² > 0`, `A` is not almost everywhere zero, so
some such section has `A(a) ≠ 0`, and dividing by `A(a)` shows that `f` is almost everywhere
strongly measurable.

Clause 4. Through `E` the pairing is `∫ A(a) f(y) · conj (A(a) f'(y)) d(α.prod ν)
= ∫ ‖A(a)‖² · f(y) conj f'(y) d(α.prod ν)`, and `integral_prod_mul` factors it as
`(∫ ‖A‖² dα) · ∫ f conj f' dν = c · ∫ f conj f' dν`.

The comparison is measure theoretic; it uses no property of Eisenstein series.

## Sources

The statement's sources are listed on the page of
`Langlands.Global.AdelicWavePacketProductPairingStatement`.
