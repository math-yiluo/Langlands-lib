# Square-integrable ambient profiles on the positive split centre

Module `Langlands.Global.AdelicAmbientWavePacketProfileStatement` states
`Langlands.Global.AmbientWavePacketProfileStatement`. It does not prove it.

| Declaration | Kind | Provenance |
| --- | --- | --- |
| `AmbientWavePacketProfileStatement` | statement | derived: see below |

## Statement

For a connected reductive `G` over a number field `F`, a linear chart
`eG : ℝ^m ≃ X^*(G) ⊗ ℝ` (`RealCharacterParameter F G`) and a smooth compactly supported
`b : ℝ^m → ℂ`, the ambient profile

`ambientWavePacketProfile eG b g = ∫ b(z) · g^{i eG(z)} d(spectralMeasure m)(z)`

(module `Langlands.Global.AdelicWavePacketAmbientLiftStatement`; `g^ν = parameterPower F G ν g`,
`spectralMeasure m = (2π)^{-m} dz`) satisfies:

1. it is continuous on `G(𝔸)`;
2. its restriction to `A_G` (`RestrictionSplitCentre.canonicalSubgroup F G`) is in `L²` for
   `positiveCentreHaarMeasure F G hG` (module `Langlands.Global.AdelicPrincipalQuotientProduct`),
   the Haar measure on `A_G` normalized against the existing Haar measures: it is the pushforward
   by `positiveCentreEquiv` of `intrinsicCentreHaarMeasure`, whose product with the Haar measure
   on the norm-one subgroup `G(𝔸)¹` is carried to the Haar measure on `G(𝔸)` by
   `intrinsicNormOneDecomposition`. The exact product decomposition of the measure on
   `G(F) \ G(𝔸)` as this measure times `canonicalMeasure F G` on `[G]` is the separate
   proposition `PrincipalQuotientProductMeasureStatement`;
3. if `b` is not the zero function, `∫_{A_G} ‖profile(a)‖² da > 0`.

The split rank `m` may be zero.

## Provenance

The profile is the function of `H_G(g)` that multiplies a relative wave packet when the relative
spectral data are tensored with the ambient coefficient `b`; it is the Fourier transform of `b`
evaluated at `H_G(g)`, in the sense recalled in the Markdown of
`Langlands.Global.AdelicSpectralDecompositionReduction`, section
`RelativeWavePacketOrthogonalityStatement`. The statement is the Fourier-analytic input that this
passage needs: the profile is square integrable on `A_G` and nonzero when `b` is. Conventions:
Getz–Hahn (2024) (`getz-hahn-2024-automorphic-representations`), §2.6, printed pp.68–69
(PDF pp.85–86), (2.19)–(2.22), for `A_G`, `G(𝔸)¹` and `[G]`; §10.5, printed pp.281–282
(PDF pp.293–294), (10.22)–(10.24), for wave packets over `i(𝔞_M^G)^*`; Bernstein–Lapid (2024)
(`bernstein-lapid-2024-meromorphic-continuation-eisenstein`), §2.1, p.190, for the character
`g ↦ e^{⟨ν, H_G(g)⟩}`. The statement does not identify `positiveCentreHaarMeasure` with Lebesgue
measure in the chart `eG`; only its Haar property enters.
