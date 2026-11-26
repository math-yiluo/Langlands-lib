# Left rational invariance of wave packets

Module `Langlands.Global.AdelicWavePacketLeftInvariance` states and proves
`Langlands.Global.WavePacketLeftRationalInvarianceStatement`, with proof
`Langlands.Global.wavePacketLeftRationalInvariance`.

## Statement

For a number field `F : Type`, a connected reductive group scheme `G` over `F` (affine, locally
of finite type), a subgroup `K` of `G(𝔸)`, a matrix representation `rho`, the smooth-structure
data `hsmooth`, `hcalc`, and a function `Θ : G(𝔸) → ℂ` with
`IsWavePacket F G K rho hsmooth hcalc Θ` (module
`Langlands.Global.AdelicWavePacketCompletenessReduction`):

`IsLeftInvariantUnder F G (rationalSubgroup F G) Θ`, that is, `Θ(γ g) = Θ(g)` for every
`γ ∈ G(F)` and every `g ∈ G(𝔸)`.

This is the first conclusion of `WavePacketConvolutionStatement` (module
`Langlands.Global.AdelicWavePacketTranslationReduction`), under fewer hypotheses: only
`IsConnectedReductive G` is assumed besides the wave packet. Maximality of `K`, closedness of
`rho` and the existence of a minimal parabolic are not used.

## Provenance

Derived. A wave packet is
`Θ(g) = ∫ ∑ j, c j x · E j (i e(x)) g d(spectralMeasure n)(x)`, where each `E j` is meromorphic
in linear coordinates with a domain of holomorphy `D` containing every imaginary parameter
`i e(x)`, and equals the Eisenstein series `E(v j, λ)` for sufficiently regular `λ`. The
Eisenstein series `E(v, λ)(g) = ∑_{γ ∈ P(F) \ G(F)} v(γ g) exp⟨λ, H_P(γ g)⟩` is a function on
`G(F) \ G(𝔸)` where it converges (Mœglin–Waldspurger, *Spectral decomposition and Eisenstein
series*, II.1.5; Lapid 2011, §2, p.311, registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`), and the invariance propagates to
the continuation by the identity theorem. The Library's
`EisensteinContinuationRationalInvarianceStatement` (module
`Langlands.Global.AdelicWavePacketRationalInvariance`) carries out that argument; this module
applies it to the data of `IsWavePacket`.

## Proof (as implemented)

1. Destructure `IsWavePacket`: the parabolic data `P, M, U, A, p, iU, l, a, r`, the
   geometric unipotent radical `hU`, the Iwasawa compact `hK`, coordinates `e`, the inducing
   forms `v j` with `IsSquareIntegrableInducedForm`, coefficients `c j`, continuations `E j`
   with domain `D`, the inclusion `Set.range (imaginaryParameter F P) ⊆ D`, the meromorphy of
   each `λ ↦ E j λ g`, the agreement with `hK.eisensteinSeries (v j)` on a regular region, and
   the formula for `Θ`. The instance `LocallyOfFiniteType P.X.hom` comes from the closed
   immersion `p` (`IsClosedSubgroup.locallyOfFiniteType`).
2. The first conjunct of `IsSquareIntegrableInducedForm` is `IsAutomorphicFunctionOn` for
   `parabolicQuotientSubgroup F p iU l`, whose first conjunct is left invariance of `v j` under
   `U(𝔸) M(F)`. With `hU`, the meromorphy and the regular agreement,
   `eisensteinContinuation_leftRationalInvariant` gives left `G(F)`-invariance of `E j λ` for
   every `λ ∈ D`.
3. `packetIntegral_leftRationalInvariant`, applied to `spectralMeasure n`, the parameter map
   `x ↦ imaginaryParameter F P (e x)`, the coefficients `c` and the continuations `E`, gives
   left `G(F)`-invariance of the packet integral. Its support hypothesis holds because every
   `imaginaryParameter F P (e x)` lies in `D`.

The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
