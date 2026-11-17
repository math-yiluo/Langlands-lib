# The Jacquet integral of spherical vectors

Lean module: `Langlands.Representation.Archimedean.ComplexSphericalJacquetNormalized`, namespace
`Langlands.Archimedean.ComplexSphericalJacquetNormalized`.

This module holds no statement definition. It shows that the Library's Jacquet integral
`ComplexJacquetDual.jacquet n` does not vanish on spherical vectors of strictly dominant
principal series with trivial phases. The result is used by `ComplexJacquetAntidominantBoundProof`.
All content is internal.

Notation (Library, `ComplexPartialJacquet`, `ComplexMaximalParabolicIntegration`):
- `IsPhasePower χ e`: `χ_l(z) = χ_l(z/|z|) (|z|²)^{e_l}`, `χ_l(1) = 1`, `|χ_l| = 1` on the
  unit circle.
- `chartGL x = J(x,1)`, the identity matrix with last row `(x, 1)`, and `iotaGL g = diag(g, 1)`.
- `jacquetStep h (g) = ∫_{ℂ^m} h(J(x,1) diag(g,1)) dx`, and
  `jacquet (m+1) h = jacquet m (jacquetStep h)`, `jacquet 0 h = h(1)`.
- `r_l(x) = partialSq x l = 1 + ∑_{j<l} |x_j|²`.

## Results

- `sum_mul_eq_sum_sub`: summation by parts with complex coefficients. If
  `T_l = ∑_{j ≥ l} t_j` and `T_0 = 0`, then
  `∑_{l ≤ m} σ_l t_l = ∑_{l<m} (σ_{l+1} - σ_l) T_{l+1}`. The proof is that of the Library's
  real version `ComplexParabolicChartBound.sum_mul_eq_sum_sub`.
- `ofReal_cpow_eq_exp`: `r^s = exp(s log r)` for `r > 0`.
- `chartExp e m l = e_{l+1} - e_l - 1`.
- `spherical_chart`: assume `IsPhasePower χ e` with trivial phases (`χ_l(z/|z|) = 1`), `f` in
  the principal series of `χ` on `GL_{m+1}(ℂ)`, and `f = 1` on `U(m+1)`. Then for
  `κ ∈ U(m+1)`, `f(J(x,1) κ) = ∏_{l<m} r_{l+1}(x)^{e_{l+1} - e_l - 1}`.
  - Write `J(x,1) κ = diag(a) u k` (Iwasawa decomposition,
    `ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary`). Then
    `f(J(x,1) κ) = χδ^{1/2}(a) = ∏_i (|a_i|²)^{s_i}` with `s_i = e_i + m/2 - i`.
  - The Library's `prod_tail_sq_eq` gives `∏_{j ≥ l} |a_j|² = r_l(x)` for `l ≤ m`.
  - Write both sides as exponentials of sums of logarithms. Summation by parts with
    `t_i = log |a_i|²` and `T_l = log r_l(x)` (`T_0 = log r_0 = 0`) identifies the exponents.
- `jacquet_ne_zero_of_spherical`: let `IsPhasePower χ e` hold with
  `Re e_{l+1} < Re e_l` for `l + 1 < n` and trivial phases. If `f` is a `U(n)`-finite function
  of the principal series of `χ` with `f = 1` on `U(n)`, then `jacquet n f ≠ 0`. Induction on
  `n`:
  - `n = 0`: `jacquet 0 f = f(1) = 1`.
  - `n = m + 1`: on `U(m)`, `jacquetStep f` is the constant
    `C = ∫ ∏_{l<m} r_{l+1}(x)^{e_{l+1}-e_l-1} dx` (`spherical_chart`). `C ≠ 0` by
    `ComplexPartialSqCpow.integral_integrand_ne_zero`, since `Re(e_{l+1} - e_l - 1) < -1`.
  - `jacquetStep f` is a `U(m)`-finite function of the principal series of the shifted
    characters (Library `jacquetStep_mem`). So `g = C⁻¹ · jacquetStep f` satisfies the
    hypotheses for `m`: phase power by `IsPhasePower.shift`, still strictly dominant, trivial
    phases, and `g = 1` on `U(m)`.
  - By `ComplexJacquetKernel.jacquet_smul`, `jacquet (m+1) f = C · jacquet m g ≠ 0`.

## Provenance

Internal. Classically, `jacquet n f` for the spherical vector is the Harish-Chandra `c`-function,
which factors over the maximal parabolic subgroups (Gindikin–Karpelevich). Here only its
nonvanishing is proved, by the explicit rank-one integrals of `ComplexPartialSqCpowIntegral`.
