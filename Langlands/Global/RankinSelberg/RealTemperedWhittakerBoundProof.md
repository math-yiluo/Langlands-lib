# Proof of the tempered Whittaker bound in every rank

Lean module: `Langlands.Global.RankinSelberg.RealTemperedWhittakerBoundProof`.

The theorem `Langlands.Global.RankinSelbergGlobal.RealTemperedWhittaker.realTemperedWhittakerBound`
proves `RealTemperedWhittakerBoundStatement` (module `RealTemperedWhittakerBound`; see
`RealTemperedWhittakerBound.md`). For every `r > 0`, every real block list `ds` of rank `r + 1`
whose blocks have exponents of real part `0`, every nonzero real scale `a`, every `W` in the exact
Whittaker model `realWhittakerModel r ds a` and every `ε > 0`, there is `C ≥ 0` with
\[
 |W(a(y)k)| \le C \exp\!\left(\tfrac12 M(y) + \epsilon \sum_j |y_j|\right)
\]
for all `y ∈ ℝ^{r+1}` and all orthogonal `k`, where `a(y)` is the positive diagonal matrix
`diag(e^{y_j})` and `M(y) = torusModularLog (r + 1) y` the logarithm of the upper unipotent modulus.

This is the scalar case of H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009),
Proposition 3.4, author p. 21, with an arbitrarily small exponential loss in place of a polynomial.
The proof below is internal: a Levi-staged open-cell integral replaces Wallach's tempered
majorization. Unprefixed names below are in the namespace
`Langlands.Global.RankinSelbergGlobal.RealLeviStages` of the helper modules.

## The model

Write `expand ds = characterList p z` (`exists_expand_eq_characterList`). The module
`RealDescendingWhittakerRange` proves `realWhittakerModel_eq_range_descendingCanonical`: the exact
model of `ds` at the scale `-a` is the range of the canonical Jacquet map of `p, z` at the scale `a`
restricted to the standard vectors of `ds` (`RealPrincipalSeries.realStandardKFinite_le_expand`).
The theorem applies it at `-a` and concludes with `temperedBound_of_mem_range` of the module
`RealSlotBlockData`.

## The analytic argument

The exponents `z` are the position exponents of `ds`: on the two positions of an induced block of
weight `k ≠ 0` they are `ν ± |k|/2` with `Re ν = 0`, and every other exponent is imaginary
(`realPositionExponent_re`). The standard vectors of `ds` have only the Fourier modes
`±(|k| + 1 + 2l)` along the rotations of these blocks (`slotModes_of_mem`). Then
`canonical_tempered_slot_bound` (module `RealSlotTemperedBound`) gives the bound for the canonical
Jacquet family at `z`, along the following route.

1. Move the exponents along the block index `μ` (the two positions of an induced block of nonzero
   weight form one block, every other position is its own block): `z(t) = z - t μ`
   (`deform`, module `RealSlotStagedFamily`). This keeps the differences `|k|` inside the blocks; `z(t)` is
   strictly dominant for large `Re t`.
2. For `z(t)` in the chamber, move the positive diagonal past the open cell
   (`additiveJacquetIntegral_torus_mul`, module `RealSlotStaged`) and integrate the open cell in Levi stages: first over the coordinates inside
   the two-by-two blocks, then over the opposite unipotent radical of their parabolic subgroup
   (`integral_cell_eq_levi`). The torus twists the additive character of the block coordinates by
   the phases `a e^{y_{rev(q+1)} - y_{rev q}}` (`twistChar_cellPt_block`).
3. The Iwasawa decomposition of the rank-two open cell in each two-by-two block, and the Fourier
   expansion along the blocks, turn the inner integral into a finite sum over the admissible mode
   lists of Fourier coefficients of the profile times products over the blocks of scalar Fourier
   transforms of angular kernels (`leviIntegral_standardSection` of `RealSlotLevi`, `core_bound` of
   `RealSlotCore`). Each such transform is bounded by the power `|k|/2` of the frequency
   (`angularKernel_fourier_bound`, module `RealDiscreteReciprocalFourier`).
   This bounds the inner integral by the powers `|phase|^{|k|/2}` times the spherical function of
   the block-averaged exponents `-Re t · μ` (`norm_leviIntegral_le_spherical`).
4. The spherical function is integrable on the opposite radical chart for `Re t > 0`
   (`integrable_spherical_lowerCGL`, module `RealSlotOuter`, from the chart theorem of
   `RealLeviChartIntegrable`). So the staged integral is holomorphic on `Re t > 0`
   (`stagedIntegral_holomorphic`). In the chamber, the canonical Jacquet family at
   `(z(t), torus y · g)` equals `stagedFamily`: the staged integral multiplied by the torus factor
   `exp(Σ_i shiftExp (z(t)) i · y_{rev i})` of the shifted exponents, the modulus
   `exp(torusModularLog y)` and the Haar normalization `haarScale r a` (`stagedIntegral_of_chamber`).
   The identity theorem extends this equality of the canonical family with `stagedFamily` to all of
   `Re t > 0` (`canonical_eq_stagedFamily`).
5. On a line `Re t = δ > 0`, the powers of the phases cancel the half weights `±|k|/2` of `Re z`, and
   the bound is `A_δ exp(M(y)/2 + r δ Σ_j |y_j|)` (`norm_canonical_deform_le`). Uniform polynomial
   growth of the canonical family on a compact disk and `smallExponentialAtZero_of_rightBoundary`
   give the loss `exp(ε Σ_j |y_j|)` at `t = 0` (`canonical_tempered_slot_bound`).

[Registered author edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
