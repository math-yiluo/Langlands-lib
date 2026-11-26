# The kernel of the ascending tail map grows slowly

Module `Langlands.Representation.Archimedean.RealTailKernelGrowth`, namespace
`Langlands.Archimedean.RealTailKernel`.

## Setting

Let `d` be an induction block of weight `m ≠ 0` and exponent `t`, `ℓ = |m|`, and let
`pre ++ [induced d] ++ post` have rank `n`. The Library's tail map
`blockFrobMap (RealInducedCharacter.data_tail hn hl hs)` (module `RealInducedCharacterMaps`)
is a surjective intertwiner from the `O(n)`-finite standard module of the ascending list

`tailList pre post d sa sb = pre ++ [character (cb d sb), character (ca d sa)] ++ post`

onto that of `pre ++ [induced d] ++ post`. Here `cb d sb = sgn^{sb} |·|^{t - ℓ/2}` and
`ca d sa = sgn^{sa} |·|^{t + ℓ/2}` sit at the positions `p = realRank pre` and `p + 1`, and
`(sa + sb) mod 2 = (ℓ + 1) mod 2`. On `O(n)` the map multiplies the `j`-th block Fourier
coefficient along the rotations `r_p(θ)` of the coordinates `p, p + 1` by the Library's tail
multiplier, which on the relevant parity class is nonzero exactly for `|j| > ℓ`.

## Results

- `lowerRootElement_eq_iwasawa`: for `p + 1 < n` and real `t`, with `S = √(1 + t²)`,
  `e(t) = 1 + t E_{p+1,p}` equals `exp(diag x) · (1 + t E_{p,p+1}) · r_p(arctan t)`, where
  `x = iwasawaExponent t` has entries `-log S` at `p`, `log S` at `p + 1` and `0` elsewhere.
- `orbit_eq_of_isExpEquivariant`: if `F(exp(diag x) u g) = exp(∑ᵢ αᵢ xᵢ) F(g)` for upper
  unipotent `u` (`IsExpEquivariant α F`), then
  `F(e(t) g) = exp((α_{p+1} - α_p) log S) · F(r_p(arctan t) g)`.
- `modePoly m m' = (1 + iX)^m (1 - iX)^m'`, `modePoly_natDegree_le`, and
  `sqrt_pow_mul_expMode`: `S^(m + m') e^{i (m - m') arctan t} = (1 + i t)^m (1 - i t)^m'`.
- `iteratedDeriv_eval_eq_zero`: a complex polynomial of degree `< k`, as a function of a real
  variable, has vanishing `k`-th derivative at `0`.
- `exponent_tailList_zero`, `exponent_tailList_one`: the position exponents of the ascending
  list at `p` and `p + 1` are `t - ℓ/2` and `t + ℓ/2`.
- `kernel_fourier_support`: if `h` lies in the kernel of the tail map and `κ ∈ O(n)`, a block
  Fourier coefficient `Φ_j h (κ) ≠ 0` forces `j` into the parity class of the pair and `|j| < ℓ`.
- `exists_poly_orbit`: for such `h` and `κ ∈ O(n)` there is a complex polynomial `Q` of degree
  `< ℓ` with `h(e(t) κ) = Q(t)` for all real `t`.
- `tailList_character_relation`: the position characters `χ` of the ascending list satisfy
  `χ_{p+1}(x) = x^ℓ χ_p(x)` for `x > 0`.
- `tailKernel_growth`: there is `C` such that for every `k` the operators of degree `≤ k` of
  `U(ℂ ⊗_ℝ 𝔤𝔩_n(ℝ))`, acting through `realStandardLie` and restricted to the kernel of the
  tail map, span a space of dimension at most `C (k + 1)^(n (n - 1) - 1)`.

## Proofs

**Iwasawa decomposition.** Compare entries, using the Library's formula for the entries of a
product with a block rotation (`RealBlockDerivative.mul_blockRotation_apply`), the diagonal of
`exp(diag x)` (`RealPrincipalSeriesDuality.matrixExpUnit_diagonal`), and
`cos(arctan t) = 1/S`, `sin(arctan t) = t/S`. In the `(p, p+1)` block,
`[[S⁻¹, 0], [0, S]] · [[1, t], [0, 1]] · [[1/S, -t/S], [t/S, 1/S]] = [[1, 0], [t, 1]]`
since `S² = 1 + t²`; off the block both sides are the identity.

**Exponential factor.** Substitute the decomposition and apply `IsExpEquivariant` to
`exp(diag x)`, the upper unipotent `1 + t E_{p,p+1}` (`upperRootElement_mem`) and
`r_p(arctan t) g`. Only the two block coordinates of `x` are nonzero.

**Modes.** Write `e^{ijθ} = (e^{iθ})^m (e^{-iθ})^{m'}` for `j = m - m'` and use
`e^{±iθ} = (1 ± i t)/S` at `θ = arctan t`. The derivative statement follows from the Library's
`RealTaylorLeftPolynomialProof.iteratedDeriv_eq_of_isLittleO`, applied to `Q` itself: the
`k`-th derivative at `0` is `k! · Q_k = 0`.

**Fourier support.** By `blockFourierCoefficient_blockFrobMap`, on `O(n)` the `j`-th coefficient
of the image is the tail multiplier at `j` times `Φ_j h`. If the image is `0` and the multiplier
is nonzero, `Φ_j h = 0` on `O(n)`. Off the parity class `Φ_j h = 0` by
`blockFourierCoefficient_eq_zero_of_not_even`; on it, `|j| = ℓ` is impossible
(`ℓ - 1` lies in the parity class), and `tailMultiplier_ne_zero_iff` gives a nonzero multiplier
for `|j| > ℓ`.

**Polynomial orbit.** `h` lies in the principal series of the position characters, so
`isExpEquivariant_of_mem_principalSeries` (with `RealBlockPosition.realPositionCharacter_exp`)
gives exponential equivariance with the `ρ`-shifted exponents `αᵢ = τᵢ + (n - 1)/2 - i`. Their
difference at the block is `α_{p+1} - α_p = (t + ℓ/2) - (t - ℓ/2) - 1 = ℓ - 1`, so
`h(e(t) κ) = S^{ℓ - 1} h(r_p(arctan t) κ)`. Fourier inversion on `O(n)`
(`RealBlockFourierFinite.exists_eq_sum_blockFourierCoefficient`) writes
`h(r_p(θ) κ) = (2π)⁻¹ ∑_{|j| ≤ D} Φ_j h(κ) e^{ijθ}`. For each `j` with `Φ_j h(κ) ≠ 0`, the
Fourier support gives `|j| ≤ ℓ - 1` and `ℓ - 1 - j` even, hence natural numbers `m, m'` with
`m + m' = ℓ - 1` and `m - m' = j`; then `S^{ℓ - 1} e^{ij arctan t} = modePoly m m'` at `t`, a
polynomial of degree `≤ ℓ - 1`. Summing gives `Q`.

**Growth.** `tailList_character_relation` follows from `realPositionCharacter_exp` and
`aExp - bExp = ℓ`. For `h` in the kernel and `κ ∈ O(n)`, the `ℓ`-fold right derivative along
`E_{p+1,p}` at `1` of the right translate of `h` by `κ` is the `ℓ`-th derivative at `0` of
`t ↦ h(e(t) κ)` (`iterate_rightDerivative_rightTranslation`), which vanishes by
`exists_poly_orbit` and `iteratedDeriv_eval_eq_zero`. The Library theorem
`realTaylorLeftPolynomial` then shows that `t ↦ h(e(t) g)` is a polynomial of degree `< ℓ` for
every `g`, and `realLeftPolynomialGrowth`, applied to the kernel as the subspace `Y`, gives the
bound.

## Provenance

The module is internal. It makes precise, for the Library's tail map, the classical fact that the
kernel of the projection of the principal series `sgn^{sb}|·|^{t-ℓ/2} × sgn^{sa}|·|^{t+ℓ/2}` of
`GL₂(ℝ)` onto the discrete series block is the `ℓ`-dimensional representation, on which the
lower unipotent group acts by polynomials of degree `< ℓ`; parabolic induction of this
finite-dimensional block gives a module of smaller Gelfand–Kirillov dimension. The growth bound is
the Library's `RealLeftPolynomialGrowthStatement` (proved by `realLeftPolynomialGrowth`), and the
passage from the Taylor condition on `O(n)` to polynomiality is the Library's
`RealTaylorLeftPolynomialStatement` (proved by `realTaylorLeftPolynomial`).
