# The ambient profile is a scaled inverse Fourier transform

Module `Langlands.Global.AdelicAmbientWavePacketProfileProof` proves
`Langlands.Global.AmbientWavePacketProfileStatement` (module
`Langlands.Global.AdelicAmbientWavePacketProfileStatement`) with no further hypothesis.

| Declaration | Kind | Content |
| --- | --- | --- |
| `ambientWavePacketProfile_squareIntegrable` | theorem (proved) | `AmbientWavePacketProfileStatement` |

The remaining declarations of the module are private.

## Proof

1. Dual coordinates. The chart `eG` determines coordinates `parameterCoordinates F G eG` on the
   real dual `RealCharacterDual F G` of `X^*(G) ⊗ ℝ`. They are injective
   (`parameterCoordinates_injective`) and onto: a vector `y ∈ ℝ^m` is attained at the dual element
   of the linear functional with values `y j` on the basis `eG(e_j)`, transported through
   `realCharacterDualEquivParameterDual`. Composed with `EuclideanSpace`, this gives a continuous
   linear isomorphism `fourierCoordinates eG : RealCharacterDual F G ≃ ℝ^m` under which the real
   pairing `⟨eG(x), H⟩` is the Euclidean inner product `⟪x, fourierCoordinates eG H⟫`, and
   `⟨i eG(x), H⟩ = i ⟨eG(x), H⟩` for the complex pairing.
2. The profile as a Fourier transform. With `B = b ∘ (EuclideanSpace ≃ ℝ^m)`, a Schwartz function
   because `b` is smooth with compact support, the definition of `spectralMeasure m` and the
   Lebesgue-preserving identification `PiLp.volume_preserving_toLp` give
   `profile(g) = S(fourierCoordinates eG (H_G(g)))` with
   `S = (2π)^{-m} · (𝓕⁻ B)(· / 2π)`, a Schwartz function. Here `H_G = characterLog F G`.
3. Continuity follows from the continuity of `S`, of `fourierCoordinates eG` and of
   `characterLog F G` on `G(𝔸)`.
4. Square integrability. `positiveCentreLogEquiv F G hG` is a topological group isomorphism from
   `A_G` onto `RealCharacterDual F G` (written multiplicatively) given by `H_G`; composed with
   `fourierCoordinates eG` it is a continuous group isomorphism `C : A_G ≃ ℝ^m`. The image of the
   Haar measure `positiveCentreHaarMeasure F G hG` under `C` is therefore an additive Haar measure
   `μV` on `ℝ^m`, and `S ∈ L²(μV)` (`SchwartzMap.memLp`). Since `profile|_{A_G} = S ∘ C`, the
   restriction is in `L²(positiveCentreHaarMeasure)`.
5. Positivity. If `b ≠ 0`, then `B ≠ 0`, so `𝓕⁻ B ≠ 0` by Fourier inversion
   (`fourier_fourierInv_eq`), so `S ≠ 0`, the dilation and the scalar `(2π)^{-m}` being
   invertible. Since `C` is onto, the restriction of the profile to `A_G` is nonzero at some
   point. It is continuous, so `‖profile‖²` has nonempty open support, which has positive Haar
   measure; with integrability of `‖profile‖²` (from step 4) this gives
   `∫_{A_G} ‖profile‖² > 0` (`integral_pos_iff_support_of_nonneg`).

No positivity of `b` and no parabolic subgroup enter the proof.

## Sources

The statement's sources are listed on the page of
`Langlands.Global.AdelicAmbientWavePacketProfileStatement`. The proof uses Mathlib's Fourier
transform on Schwartz space and Fourier inversion.
