# Lifting relative wave packets by an ambient spectral coefficient

Module `Langlands.Global.AdelicWavePacketParabolicAmbientLiftProof` proves
`Langlands.Global.WavePacketParabolicAmbientLiftStatement` (module
`Langlands.Global.AdelicWavePacketParabolicAmbientLiftStatement`) and
`Langlands.Global.WavePacketAmbientLiftStatement` (module
`Langlands.Global.AdelicWavePacketAmbientLiftStatement`) from
`Langlands.Global.EisensteinRegularParameterStatement`, the nonemptiness of every
regular-parameter region, which it takes as a hypothesis and does not prove.

| Declaration | Kind | Content |
| --- | --- | --- |
| `wavePacketParabolicAmbientLift_of_regularParameter` | theorem (proved) | `EisensteinRegularParameterStatement → WavePacketParabolicAmbientLiftStatement` |
| `isWavePacket_of_isParabolicWavePacket` | theorem (proved) | `IsParabolicWavePacket … Θ → IsWavePacket F G K rho hsmooth hcalc Θ` |
| `wavePacketAmbientLift_of_regularParameter` | theorem (proved) | `EisensteinRegularParameterStatement → WavePacketAmbientLiftStatement` |

## The lift

Let `Θ(g) = ∫ ∑ j, c j x · E j (i e(x)) g d(spectralMeasure n)(x)` be a wave packet of `P` over
`i(𝔞_M^G)^*` (`IsRelativeWavePacket`), with chart `e : ℝⁿ ≃ relativeParameterSpace p`, and let
`eG : ℝ^m ≃ X^*(G) ⊗ ℝ` be a chart and `b` a smooth compactly supported coefficient on `ℝ^m`. The
profile is `ambientWavePacketProfile eG b g = ∫ b(z) g^{i eG(z)} d(spectralMeasure m)(z)`.

`wavePacketParabolicAmbientLift_of_regularParameter` proves that `g ↦ profile(g) · Θ(g)` is a
wave packet of the same presented parabolic over all of `i𝔞_P^*` (`IsParabolicWavePacket`, for
the same `hK`, `iU`, `l`, `r`, `hA`, `hT`), with

- the chart `e' : ℝ^{n+m} ≃ X^*(P) ⊗ ℝ`, the composite of `(spectralCoordinateProduct n m).symm`
  (splitting `ℝ^{n+m}` into its relative block `ℝⁿ` and its ambient block `ℝ^m`; the module
  `Langlands.Global.AdelicSpectralCoordinateProduct` defines `spectralCoordinateProduct n m` as
  the concatenation `ℝⁿ × ℝ^m ≃ ℝ^{n+m}`), `e × eG`, and `relativeAmbientParameterEquiv r hG`
  (`(x, z) ↦ x + p*z`, an isomorphism `relativeParameterSpace p × X^*(G) ⊗ ℝ ≃ X^*(P) ⊗ ℝ`, module
  `Langlands.Global.AdelicRelativeAmbientParameterProduct`); thus
  `e'(spectralCoordinateProduct n m (x, z)) = relativeAmbientParameterEquiv r hG (e x, eG z)`;
- the coefficients `c' j = spectralProductCoefficient (c j) b`, `(x, z) ↦ c j x · b z`, smooth and
  compactly supported (`ContDiff.spectralProductCoefficient`,
  `HasCompactSupport.spectralProductCoefficient`);
- the same inducing forms `v j`, continuations `E j`, holomorphy domain `D` and regularity
  thresholds.

Proof of the integral identity at a fixed `g`. By
`imaginaryParameter_relativeAmbientParameterEquiv`, the imaginary parameter of `e'(x, z)` is
`i e(x) + p*(i eG(z))`. Both `i e(x)` and this point lie in `D`, which contains the imaginary
parameters. The ambient shift `ν = i eG(z)` has real part zero
(`parameterRealPart_imaginaryParameter`), so
`eisensteinContinuationAmbientShift_of_regularParameter` (module
`Langlands.Global.AdelicEisensteinAmbientShiftProof`) gives
`E j (i e(x) + p*ν) g = g^ν · E j (i e(x)) g`. Hence the integrand of the new packet at
`(x, z)` is `f(x) · B(z)` with `f(x) = ∑ j, c j x · E j (i e(x)) g` and `B(z) = b(z) g^{i eG(z)}`.
`integral_spectralProductCoefficient` (module `Langlands.Global.AdelicSpectralCoordinateProduct`)
factors the integral over `ℝ^{n+m}` with `spectralMeasure (n + m)` as
`(∫ f d(spectralMeasure n)) · (∫ B d(spectralMeasure m)) = Θ(g) · profile(g)`.

`isWavePacket_of_isParabolicWavePacket`: `IsWavePacket` quantifies the presented parabolic
existentially, together with `IsClosedImmersion (iU ≫ p)`, which follows from the geometric
unipotent radical and the closed immersion `p`. The remaining data are the same.

`wavePacketAmbientLift_of_regularParameter` composes the two.

## Sources

Getz–Hahn (2024) (`getz-hahn-2024-automorphic-representations`), §10.5, printed pp.281–282
(PDF pp.293–294), (10.22)–(10.24): wave packets over `i(𝔞_M^G)^*` on `[G]`. Lapid 2011
(`lapid-2011-asymptotic-inner-product-truncated-eisenstein`), §3, printed p.314 (PDF p.323): wave
packets `Θ_{P,φ}` over `i𝔞_P^*`. The passage between the two, by tensoring with a function of the
ambient parameter whose Fourier transform is the profile, is the one described in the Markdown of
`Langlands.Global.AdelicSpectralDecompositionReduction`, section
`RelativeWavePacketOrthogonalityStatement`; this module proves it for the Library's packets.
