# Isolating one class of a finite central-character fiber

Waldspurger (2003), proof of Theorem VIII.4.2, printed p.330 (PDF p.96),
computes `(p_χ f_ψ)(g) = Σ_{ω' ∈ 𝒪_χ} (E^G_G ψ_{ω'})(g)` for a wave packet
`f_ψ` on the unitary unramified orbit `𝒪` of a discrete series `ω`. The
fiber `𝒪_χ = {ω' ∈ 𝒪 ; χ_{ω'} = χ}` is finite. He then says: "Pour tout
`ϕ ∈ 𝒜(ω)`, on peut trouver `ψ ∈ C^∞(𝒪, G)` tel que `ψ_{ω'} = 0` si
`ω' ∈ 𝒪_χ − {ω}` et `E^G_G ψ_ω = ϕ`." This module supplies the
isolation part of that sentence on the Library's actual orbit, for the
`M = G` packet `rationalOrbitWavePacket` of
`RationalOrbitWavePacketPairing` and its central projection in
`RationalOrbitCentralProjection`. The construction of the isolating
function is internal to this project.

## Torus lemmas

The torus is `J → Circle` for a finite type `J`. A function on it is
smooth (`IsSmoothFiniteTorusFunction`) when its composite with the
real-angle covering `finiteTorusExp` is `C^∞`.

- `isSmoothFiniteTorusFunction_coord`: each coordinate
  `z ↦ (z j : ℂ)` is smooth. Through the covering it is
  `x ↦ exp(i x_j)`.
- `exists_isSmoothFiniteTorusFunction_lagrange`: for a finite set `Z` and
  a point `z₀` there is a smooth `p` with `p z₀ = 1` and `p w = 0` for
  `w ∈ Z`, `w ≠ z₀`. For each such `w` the proof chooses a coordinate `j`
  with `w j ≠ z₀ j` and takes
  `p = ∏_w ((z j) − (w j)) / ((z₀ j) − (w j))`. A finite product of
  smooth functions is smooth (`contDiff_prod`).
- `isSmoothFiniteTorusFunction_sum_mul_const`: a finite sum of
  translates `z ↦ p (z * c i)` of a smooth function is smooth, by the
  published `isSmoothFiniteTorusFunction_mul_const_iff`.

## The actual orbit

The setting is that of `RationalOrbitCentralProjection`: rational points
of an affine group scheme `G` of locally finite type over a
nonarchimedean local field, a central `s : T → G` with point image `A_G`,
a Haar measure `mu` on `G(F)/A_G`, the finite-index premise `hindex` on
the split valuation image, and connected reductivity `hG`. The orbit
`𝒪` of `omega` is `discreteSeriesOrbit`. Its smooth scalar functions
form the published algebra `rationalSmoothOrbitFunctions s hs mu hG omega`
(smoothness of the pullback along `rationalDiscreteSeriesOrbitCoordinateMap`).

`exists_rationalSmoothOrbitFunction_isolating`: for every finite set `Φ`
of classes of the orbit and every class `ω₁`, there is
`f ∈ rationalSmoothOrbitFunctions s hs mu hG omega` with `f ω₁ = 1` and
`f x = 0` for `x ∈ Φ`, `x ≠ ω₁`. The proof proceeds as follows.

1. The coordinate map `c z = e⁻¹(z) • omega` (with `e` the published
   coordinates `rationalCanonicalUnitaryUnramifiedCharacterCoordinates`)
   is surjective. Two points have the same image exactly when they differ
   by `e χ` for `χ` in the stabilizer of `omega`. That stabilizer is
   finite by `finite_rationalDiscreteSeriesStabilizer` (this uses `hindex`).
2. Hence the preimage `Z` of `Φ ∪ {ω₁}` is finite. With `c z₁ = ω₁`,
   Lagrange interpolation gives a smooth `p` with `p z₁ = 1` and `p = 0`
   on `Z − {z₁}`.
3. The average `p̄ z = Σ_{χ ∈ Stab} p (z * e χ)` is smooth and invariant
   under the stabilizer. On a point of `Z` over `ω₁` it equals `1`: only
   the term `χ = 1` survives, because `z₁ * e χ ≠ z₁` for `χ ≠ 1`. On a
   point over a class of `Φ − {ω₁}` it equals `0`.
4. Invariance makes `f ω = p̄ z`, for any `z` with `c z = ω`, well defined.
   Then `f ∘ c = p̄`, so `f` is smooth on the orbit.

`integral_central_rationalOrbitWavePacket_isolated`: let `η` be a
continuous character of `A_G`, `μ_A` a left-invariant measure on `A_G`,
and `ω₁` a class of the fiber `rationalOrbitCentralFiber s hs mu omega η`.
Then there is one `f` as above, with `f ω₁ = 1`, such that for every
section `ψ` and every `g` the following holds. Assume
`x ↦ (E^G_G ψ_x)(g)` is continuous and `a ↦ f_{f•ψ}(a g)` is
`μ_A`-integrable. Then

`∫_{A_G} η(a⁻¹) f_{f•ψ}(a g) dμ_A(a) = μ_A(A_G ∩ G¹) (E^G_G ψ_{ω₁})(g)`.

Here `f_{f•ψ}` is `rationalOrbitWavePacket` of the section `x ↦ f x • ψ x`.
The proof applies the finite-fiber isolation to `Φ = 𝒪_η`, which is
finite by `finite_setOf_rationalOrbitCentralCharacter_eq`. The section
`f • ψ` vanishes on `𝒪_η − {ω₁}`, and its coefficients
`x ↦ f x · (E^G_G ψ_x)(g)` are continuous because `f` is continuous
(`IsSmoothRationalOrbitFunction.continuous`). The published
`integral_central_rationalOrbitWavePacket_of_vanishing` then applies, and
`f ω₁ = 1`. The factor `μ_A(A_G ∩ G¹)` is kept exactly as in that
theorem. The orbit measure is the published I.1-normalized
`rationalNormalizedDiscreteSeriesOrbitMeasure`, not replaced by a
probability measure. The elaboration of this statement uses an explicit
finite heartbeat limit.

## Recorded proposition

`RationalOrbitFiberIsolationStatement.{u,uV}` quantifies the orbit
isolation over every structural choice of the setting above: the field,
the group scheme, the central `s`, the quotient measure, `hindex` and
`hG`. Its conclusion is that of
`exists_rationalSmoothOrbitFunction_isolating`.
`rationalOrbitFiberIsolation` proves it by that theorem. The proposition
is an internal interface for the lower inclusion of Theorem VIII.4.2 and
adds no hypothesis to any target.

## What this module does not provide

It does not construct a section `ψ` whose value at `ω₁` is a prescribed
coefficient tensor. It does not prove that the packet `f_{f•ψ}` is a
cuspidal Schwartz function (Waldspurger VI.3.1 and VII.2.5). It does not
prove the integrability of `a ↦ f_{f•ψ}(a g)`, and it does not prove
that `μ_A(A_G ∩ G¹)` is nonzero and finite. These remain inputs of the
lower inclusion of Theorem VIII.4.2.
