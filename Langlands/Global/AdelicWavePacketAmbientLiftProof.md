# Lift of relative wave packets by ambient spectral coefficients

Module `Langlands.Global.AdelicWavePacketAmbientLiftProof` proves
`Langlands.Global.WavePacketAmbientLiftStatement` (module
`Langlands.Global.AdelicWavePacketAmbientLiftStatement`) unconditionally.

| Declaration | Kind | Content |
| --- | --- | --- |
| `wavePacketAmbientLift` | theorem (proved) | `WavePacketAmbientLiftStatement` |

## The statement

For an actual presented parabolic `P` of a connected reductive group `G` over a number
field, with geometric unipotent radical `U` and Iwasawa compact subgroup `K`, let `Θ` be a
relative wave packet of `P` over `i(𝔞_M^G)^*` (`IsRelativeWavePacket`). Let
`eG : ℝ^m ≃ X^*(G) ⊗ ℝ` be a linear chart of the ambient real character space and `b` a
smooth compactly supported coefficient on `ℝ^m`. The ambient profile is
`ambientWavePacketProfile eG b g = ∫ b(z) g^{i eG(z)} d(spectralMeasure m)(z)`. The statement
asserts that `g ↦ ambientWavePacketProfile eG b g · Θ(g)` is a full wave packet
(`IsWavePacket`) for the same `G`, `K`, `rho`, `hsmooth` and `hcalc`. The relative and
ambient parameter spaces and the spectral measures are those of the statement; the proof
changes none of them.

## The proof

The proof is one term:
`wavePacketAmbientLift_of_regularParameter eisensteinRegularParameter`.

- `Langlands.Global.wavePacketAmbientLift_of_regularParameter` (module
  `Langlands.Global.AdelicWavePacketParabolicAmbientLiftProof`) proves
  `EisensteinRegularParameterStatement.{0} → WavePacketAmbientLiftStatement`.
- `Langlands.Global.eisensteinRegularParameter` (module
  `Langlands.Global.AdelicEisensteinRegularParameterProof`) proves
  `EisensteinRegularParameterStatement.{u}` for every universe `u`: every regular-parameter
  region of a presented parabolic of a connected reductive group is nonempty. Lean
  instantiates it at universe `0`, the universe of the number field `F : Type` in the
  target statement.

The conditional lift works as follows. Write
`Θ(g) = ∫ ∑ j, c j x · E j (i e(x)) g d(spectralMeasure n)(x)`, with relative chart
`e : ℝⁿ ≃ relativeParameterSpace p`, inducing forms `v j`, continuations `E j` and common
holomorphy domain `D`. The lift keeps `v j`, `E j`, `D` and the regularity thresholds. It
uses the concatenated chart `ℝ^{n+m} ≃ ℝⁿ × ℝ^m ≃ relativeParameterSpace p × X^*(G) ⊗ ℝ ≃
X^*(P) ⊗ ℝ`, which sends `(x, z)` to `e(x) + p*(eG(z))`, and the product coefficients
`(x, z) ↦ c j x · b z`. On `D`, the ambient shift of the continued Eisenstein series,
`E j (λ + p*ν) g = g^ν · E j λ g` for `ν = i eG(z)`, holds by
`eisensteinContinuationAmbientShift_of_regularParameter`; that is where the nonemptiness of
the regular region enters. The integral over `ℝ^{n+m}` against `spectralMeasure (n + m)` then
splits into the integral against `spectralMeasure n` times the integral against
`spectralMeasure m` (`integral_spectralProductCoefficient`). This gives
`Θ(g) · ambientWavePacketProfile eG b g`. The resulting packet of the fixed parabolic is a
full packet, `IsWavePacket` (`isWavePacket_of_isParabolicWavePacket`). The Markdown of
`Langlands.Global.AdelicWavePacketParabolicAmbientLiftProof` gives the details.

`wavePacketAmbientLift` depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Sources

The packets being compared follow two sources:

- E. Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein series*,
  Clay Math. Proc. 13 (2011), §3, the wave packet `Θ_{P,φ}(g) = ∫_{i𝔞_P^*} E_P(g, φ(λ), λ) dλ`
  displayed before Proposition 2, printed p. 314 (PDF p. 323). This is the full-parameter
  convention of `IsWavePacket`. Source ID
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein`, file SHA-256
  `760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`.
- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations* (2024), §10.5,
  (10.22)–(10.24), printed pp. 281–282 (PDF pp. 293–294): packets over `i(𝔞_M^G)^*` on
  `[G]`. This is the relative convention of `IsRelativeWavePacket`. Source ID
  `getz-hahn-2024-automorphic-representations`, file SHA-256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.

Neither source states the lift as a separate result. The lift is derived: it tensors a
relative packet with a function of the ambient parameter whose Fourier transform is the
profile, as the Markdown of `Langlands.Global.AdelicWavePacketParabolicAmbientLiftProof`
explains.
