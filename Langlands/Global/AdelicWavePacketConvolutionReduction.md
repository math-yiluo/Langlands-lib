# Reduction of the convolution stability of wave packets

Module `Langlands.Global.AdelicWavePacketConvolutionReduction` states
`Langlands.Global.WavePacketConvolutionReductionStatement` and proves it
(`wavePacketConvolutionReduction`):

```
EisensteinMeromorphicContinuationStatement.{0} → EisensteinImaginaryAxisHolomorphyStatement →
  InducedConvolutionFiniteSpanStatement → WavePacketConvolutionStatement
```

The premises are:

- `EisensteinMeromorphicContinuationStatement` (module
  `Langlands.Global.AdelicEisensteinContinuationStatement`): Bernstein–Lapid 2024, Theorem 2.3
  (1), in the Fréchet form of the Corollary of §8.6;
- `EisensteinImaginaryAxisHolomorphyStatement` (module
  `Langlands.Global.AdelicEisensteinImaginaryHolomorphyStatement`): Lapid 2011, Proposition 6;
- `InducedConvolutionFiniteSpanStatement` (module
  `Langlands.Global.AdelicInducedConvolutionFiniteSpanStatement`): the functions
  `I(λ, φ) v`, for `v ∈ A^2_P` and a test function `φ` of `IsLeftFiniteTestFunction`, lie in the
  span of finitely many elements of `A^2_P` with entire coefficients (Mœglin–Waldspurger I.2.17
  and IV.1.7 (*); the comparison of the proposition's scope with theirs is in
  `AdelicInducedConvolutionFiniteSpanStatement.md`).

The conclusion is the Library statement `WavePacketConvolutionStatement` (module
`Langlands.Global.AdelicWavePacketTranslationReduction`): every wave packet `Θ`
(`IsWavePacket`) is left `G(F)`-invariant, and `R(φ) Θ` is a wave packet for every `φ` with
`IsLeftFiniteTestFunction`. The module asserts nothing about whether the premises hold; it does
not prove any of them. The absolute convergence of Eisenstein series is used through the
Library's proof `eisensteinAbsoluteConvergence`.

## Provenance

Derived: this is the route described for `WavePacketConvolutionStatement` in
`AdelicWavePacketTranslationReduction.md` (Arthur 2005, §7, the operator `I_P(λ, y)` on p.33
and the identity `E(x, I_P(λ, y) φ, λ) = E(x y, φ, λ)` on p.34; Mœglin–Waldspurger II.1.5,
IV.1.7 (*) and the finiteness theorem of I.2.17; Bernstein–Lapid, Theorem 2.3; Lapid 2011,
Proposition 6), with the finite-dimensionality and entire-coefficient step isolated as
`InducedConvolutionFiniteSpanStatement`. The implemented argument uses the Fréchet form of the
continuation to obtain joint continuity and meromorphy of the convolved continuations; it does
not use the root-hyperplane description of the singularities.

## Declarations

| Declaration | Kind |
| --- | --- |
| `exists_continuousOn_eisensteinContinuation` | theorem |
| `rightConvolution_eisensteinContinuation_eq` | theorem |
| `continuous_eisensteinContinuation_imaginary` | theorem |
| `rightConvolution_packet_eq` | theorem |
| `isMeromorphicInCoordinatesOn_univ_of_isHolomorphicInCoordinatesOn` | theorem |
| `isWavePacket_rightConvolution_of_premises` | theorem |
| `WavePacketConvolutionReductionStatement` | statement |
| `wavePacketConvolutionReduction` | theorem (proof of the statement) |

A *pointwise continuation* `(E, D)` of the Eisenstein series of `φ` is as in
`AdelicEisensteinContinuationLocalFrechet.md`: every `λ ↦ E λ g` is meromorphic in linear
coordinates with domain of holomorphy `D`, and `E λ = E(φ, λ)` for `R`-regular `λ`.

## Proofs as implemented

### Joint continuity

`exists_continuousOn_eisensteinContinuation`: assume the continuation statement, `N > 0`, and a
pointwise continuation `(E, D)` of `E(φ, ·)` for `φ` automorphic on `U(𝔸) M(F) \ G(𝔸)`. In a
linear chart `e₀`, every parameter `λ₀ ∈ D` has an open neighbourhood `T` of `e₀⁻¹ λ₀`, inside
`e₀⁻¹ D`, on which `(s, g) ↦ E (e₀ s) g` is continuous on `T × G(𝔸)`. It combines
`exists_local_frechet_of_eisensteinContinuation` and `continuousOn_of_local_frechet` (module
`Langlands.Global.AdelicEisensteinContinuationLocalFrechet`); holomorphy of `s ↦ E (e₀ s) g` on
`e₀⁻¹ D` comes from the meromorphy of `E`.

`continuous_eisensteinContinuation_imaginary`: if moreover `D` contains every imaginary
parameter, then `(x, g) ↦ E (i e(x)) g` is continuous on `ℝⁿ × G(𝔸)` for real coordinates
`e : ℝⁿ ≃ X^*(P) ⊗ ℝ`. Let `e₀` be the chart of `Module.finBasis`; the map
`x ↦ e₀⁻¹ (i e(x))` is real linear between finite-dimensional spaces, hence continuous, and the
previous result applies at each point.

### The continued convolution identity

`rightConvolution_eisensteinContinuation_eq`: assume the continuation statement, `N > 0`,
`v` and `w i` automorphic on `U(𝔸) M(F) \ G(𝔸)`, a continuous compactly supported `φ`, entire
`b i`, and `I(λ, φ) v = ∑ i, b i λ • w i` for every `λ`. Let `(E, D)` be a pointwise
continuation of `E(v, ·)` and `(E' i, D')` pointwise continuations of the `E(w i, ·)` with one
domain. Then for every `λ₀ ∈ D ∩ D'` and every `g`,
`R(φ)(E λ₀)(g) = ∑ i, b i λ₀ · E' i λ₀ g`.

1. *Meromorphy of the left side.* With `Φ s = E (e₀ s)`,
   `exists_isMeromorphicOn_rightConvolution` gives a domain `U₀` on which every
   `s ↦ R(φ)(E (e₀ s))(g)` is meromorphic; `isMeromorphicInCoordinatesOn_of_coordinates` makes
   `λ ↦ R(φ)(E λ)(g)` meromorphic in coordinates with domain `e₀ '' U₀`.
2. *Meromorphy of the right side.* Entire functions are meromorphic with domain the whole space
   (`isMeromorphicInCoordinatesOn_univ_of_isHolomorphicInCoordinatesOn`). Products
   (`IsMeromorphicInCoordinatesOn.mul`) and a finite sum over the common domain
   `S = ⋂ i, univ ∩ D'` (`IsMeromorphicInCoordinatesOn.sum`; `S = D'` if there is at least one
   index, the whole space otherwise) give meromorphy of `λ ↦ ∑ i, b i λ · E' i λ g` with domain
   `S`.
3. *Agreement on a regular region.* `eisensteinAbsoluteConvergence` gives thresholds for `v` and
   every `w i`; take `R_s` at least all these and the regularity thresholds of `E` and the
   `E' i`. For `R_s`-regular `λ`: `E λ = E(v, λ)`; the summable majorant of the terms of
   `E(v, λ)` on the compact set `g · tsupport φ` gives
   `R(φ) E(v, λ)(g) = E(I(λ, φ) v, λ)(g)`
   (`IsIwasawaCompact.rightConvolution_eisensteinSeries_eq_inducedConvolution`);
   the finite span rewrites `I(λ, φ) v`; summability of the terms of every `E(w i, λ)` at `g`
   gives linearity (`IsIwasawaCompact.eisensteinSeries_sum_mul`); and `E(w i, λ) = E' i λ`.
4. *Identity theorem.* `ParabolicRootPresentation.eqOn_of_regularParameter` gives equality on
   `e₀ '' U₀ ∩ S`.
5. *The point `λ₀`.* Joint continuity of `E` near `λ₀` (step "Joint continuity") and compact
   support of `φ` make `s ↦ R(φ)(E (e₀ s))(g)` continuous on a neighbourhood `T` of
   `e₀⁻¹ λ₀` (`continuousOn_integral_of_compact_support`). The right side is continuous on
   `e₀⁻¹ S`, where each `E' i (e₀ ·) g` is holomorphic. The set `e₀⁻¹ (e₀ '' U₀ ∩ S)` is open
   and dense, so the equality extends to `T ∩ e₀⁻¹ S`, which contains `e₀⁻¹ λ₀`
   (`EqOn.of_subset_closure`).

### Fubini

`rightConvolution_packet_eq`: for a measure `ν` on `ℝⁿ` finite on compact sets, continuous
compactly supported `φ` and `c j`, and jointly continuous `Φ j`,
`R(φ)(y ↦ ∫ ∑ j, c j x Φ j x y dν(x))(g) = ∫ ∑ j, c j x R(φ)(Φ j x)(g) dν(x)`. The function
`(h, x) ↦ φ(h) ∑ j, c j x Φ j x (g h)` is continuous with compact support in
`tsupport φ × ⋃ j, tsupport (c j)`, so `integral_integral_swap_of_hasCompactSupport` exchanges
the integrals (no σ-finiteness of the Haar measure is needed). The inner integral is split by
linearity (`integral_finsetSum`, `integral_const_mul`).

### Assembly

`isWavePacket_rightConvolution_of_premises`: destructure `IsWavePacket` (parabolic data, `hK`,
coordinates `e`, inducing forms `v j`, coefficients `c j`, continuations `E j` with domain `D`).

- *Case `N = 0`.* `G(𝔸)` has one element (`subsingleton_adelicGroupPoints_of_rank_zero`), so
  `R(φ) Θ = (∫ φ) Θ`; the same data with coefficients `(∫ φ) c j` present it.
- *Case `N > 0`.* For each `j`, `InducedConvolutionFiniteSpanStatement` gives `w j i ∈ A^2_P` and
  entire `b j i` with `I(λ, φ) v j = ∑ i, b j i λ • w j i`. Index the family `(w j i)` by
  `Fin (∑ j, m j)` through `finSigmaFinEquiv`. The Library's
  `eisensteinImaginaryContinuationBridge` (from the continuation and imaginary-holomorphy
  premises and `eisensteinAbsoluteConvergence`) gives pointwise continuations `E'` of their
  Eisenstein series with one domain `D'` containing every imaginary parameter. The new
  coefficients are `c' (j, i)(x) = c j x · b j i (i e(x))`; they are smooth
  (`contDiff_comp_imaginaryParameter`, module `Langlands.Global.AdelicSymmetricFamilyDensity`)
  and compactly supported. The new packet keeps the parabolic data, `hK`, `n` and `e`. Its
  formula: `rightConvolution_packet_eq` (with the joint continuity of each `E j` along the
  imaginary axis and `spectralMeasure n` finite on compact sets) moves `R(φ)` inside, then
  `rightConvolution_eisensteinContinuation_eq` at `λ = i e(x) ∈ D ∩ D'` replaces
  `R(φ)(E j (i e(x)))(g)` by `∑ i, b j i (i e(x)) · E' (j, i) (i e(x)) g`, and the sum over
  `j` and `i` is reindexed as the sum over `Fin (∑ j, m j)` (`Equiv.sum_comp`,
  `Fintype.sum_sigma`).

`wavePacketConvolutionReduction`: the first conclusion is
`wavePacketLeftRationalInvariance` (module `Langlands.Global.AdelicWavePacketLeftInvariance`),
the second `isWavePacket_rightConvolution_of_premises`.

All theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Scope

The module proves the implication only. Its three premises are statements of the Library that
this module does not prove.
