# The quotient-product pairing for ambient lifts

Module `Langlands.Global.AdelicWavePacketProductPairingStatement` defines the lift
`ambientProfileQuotientLift` of functions on `[G]` to `G(F) \ G(𝔸)` and states
`Langlands.Global.WavePacketProductPairingStatement`. It does not prove the statement.

| Declaration | Kind | Provenance |
| --- | --- | --- |
| `ambientProfileQuotientLift` | definition | internal: see below |
| `WavePacketProductPairingStatement` | statement | derived: see below |

## The lift

For `hG : IsConnectedReductive G`, a chart `eG : ℝ^m ≃ X^*(G) ⊗ ℝ`, a coefficient `b` and
`f : [G] → ℂ`, `ambientProfileQuotientLift hG eG b f : G(F) \ G(𝔸) → ℂ` sends `q` to
`ambientWavePacketProfile eG b a · f(y)`, where `(a, y) ∈ A_G × [G]` is the image of `q` under
`principalQuotientProductEquiv F G hG` (module `Langlands.Global.AdelicPrincipalQuotientProduct`),
the identification `G(F) \ G(𝔸) ≅ A_G × [G]` that sends the class of `a · n` (`a ∈ A_G`,
`n ∈ G(𝔸)¹`) to `(a, [n])`.

## Statement

For `G` connected reductive over a number field, a chart `eG` and a smooth compactly supported
`b ≠ 0`, put `c = ∫_{A_G} ‖ambientWavePacketProfile eG b a‖² da` for
`positiveCentreHaarMeasure F G hG`. Then

1. `0 < c`;
2. on representatives the lift is the pointwise product with the profile: for every `f` and every
   `g ∈ G(𝔸)`, `lift f [g] = profile(g) · f([g])`, with `[g]` the classes of `g` in
   `G(F) \ G(𝔸)` and in `[G]`;
3. for every `f : [G] → ℂ`, the lift is in `L²(G(F) \ G(𝔸), rationalQuotientHaarMeasure F G)` if
   and only if `f ∈ L²([G], canonicalMeasure F G)` (measurability included, as part of `MemLp`);
4. for `f, f' ∈ L²([G])`,
   `∫_{G(F) \ G(𝔸)} lift f · conj (lift f') = c · ∫_{[G]} f · conj f'`.

## Provenance

`G(F) \ G(𝔸)` is the product of `A_G` and `[G] = A_G G(F) \ G(𝔸)` by Getz–Hahn (2024)
(`getz-hahn-2024-automorphic-representations`), §2.6, printed pp.68–69 (PDF pp.85–86), Lemma 2.6.2
and (2.19)–(2.22). The Markdown of `Langlands.Global.AdelicSpectralDecompositionReduction`,
section `RelativeWavePacketOrthogonalityStatement`, describes the passage from wave packets on
`G(F) \ G(𝔸)` over `i𝔞_P^*` (Lapid 2011, `lapid-2011-asymptotic-inner-product-truncated-eisenstein`,
§3, printed p.314, PDF p.323) to wave packets on `[G]` over `i(𝔞_M^G)^*` (Getz–Hahn §10.5, printed
pp.281–282, PDF pp.293–294): tensoring the coefficients of a relative packet with an ambient
coefficient `b` gives a full packet equal to the relative packet times the ambient profile of `b`
(its Fourier transform evaluated at `H_G(g)`), and inner products on `G(F) \ G(𝔸) ≅ A_G × [G]`
factor accordingly. For the packets constructed this way, the product with the profile is
`wavePacketParabolicAmbientLift_of_regularParameter` (module
`Langlands.Global.AdelicWavePacketParabolicAmbientLiftProof`). The
statement is that factorization for the Library's quotient measures, with the constant `c` for the
measure `positiveCentreHaarMeasure` fixed by the product decomposition. It asserts nothing about
wave packets themselves; clause 2 lets it be applied to a packet that is invariant under
`A_G G(F)`.
