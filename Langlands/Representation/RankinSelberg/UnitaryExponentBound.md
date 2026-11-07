# The exponent bound for unitary generic unramified representations

Author: Worker 1797. Module `Langlands.Representation.RankinSelberg.UnitaryExponentBound`,
namespace `Langlands.RankinSelberg.UnramifiedUnitary`.

This helper module serves the proof of
`Langlands.RankinSelberg.UnramifiedUnitaryPoleFreeStatement` (see
`UnramifiedUnitaryPoleFreeProof.md`). It proves `|χ_i(ϖ)| < q^(1/2)` for the inducing
characters of a unitarizable unramified generic constituent of `GL_(k+2)(F)`, assuming the
additive character has conductor `O`. In the source this fact is implicit in
Jacquet–Shalika, *Euler products II*, Proposition 1.5(iii), printed p. 782 (literature id
`jacquet-shalika-1981-euler-products-ii`). That proposition derives pole-freeness from the
convergence of `Ψ(s, W, W')` for `Re s ≥ 1`, which rests on Euler products I,
Proposition (1.3) (see `UnitaryCellBound.md`). The implemented route is internal: it
evaluates the square-summability of `UnitaryCellMasses.rowSum_bounded` on the explicit
single-row spherical values.

## Decay of a series inverse to a polynomial (section `Decay`)

`norm_lt_one_of_mul_prod_eq_one`: let `u : ℕ → ℂ` and `b : ι → ℂ` satisfy
`(∑ u_m t^m) · ∏_i (1 - b_i t) = 1` in `ℂ⟦t⟧`, with `u_m → 0`. Then every `|b_i| < 1`.

Proof. Fix `i` and let `g = ∏_{j ≠ i} (1 - b_j t)`, a polynomial. Since
`(∑ b_i^m t^m)(1 - b_i t) = 1` (rescaled `mk_one_mul_one_sub_eq_one`), cancelling
`1 - b_i t` gives `g · ∑ u_m t^m = ∑ b_i^m t^m`. For `m ≥ deg g`, comparing coefficients
gives `b_i^m = ∑_{c ≤ deg g} g_c u_(m-c)`. This is a fixed finite combination of shifts of
`u`, so it tends to `0`. If `|b_i| ≥ 1` then `|b_i^m| ≥ 1`, a contradiction.

## Single-row Schur functions (section `SingleRow`)

- `rowExponent n m : Fin (n+2) → ℤ` is `(m, 0, …, 0)`. `rowExponent_isPartition`: it is a
  partition exponent (antitone and nonnegative). `rowExponent_last`: its last entry is
  `0`.
- `jacobiTrudi_rowExponent`: the published Jacobi–Trudi determinant `det(h_(α_i - i + j))`
  of `(m, 0, …, 0)` is the complete homogeneous symmetric polynomial `hsymm m`. The matrix
  is upper triangular: below the diagonal the index `j - i` is negative. Its diagonal is
  `(h_m, h_0, …, h_0)`.
- `satakeSchur_rowExponent`: the published `satakeSchur x (m, 0, …, 0)` equals
  `h_m(x)`.
- `halfModulus_rowExponent`: the published `halfModulus q (m, 0, …, 0)` equals
  `(√q)^(-(n+1) m)`.
- `rescale_C_eq`, `hsymm_series_mul_prod`: for any `a` and `c`,
  `(∑_m c^m h_m(a) t^m) · ∏_i (1 - a_i c t) = 1`. This is the image of the published
  `completeSeries_mul_elementaryProduct` under evaluation at `a` followed by
  `PowerSeries.rescale c`.

## The bound for characters of conductor `O` (section `Bound`)

`norm_characterValues_lt_sqrt F k π ψ hψ χ hgen hunit i`: let `ψ` have conductor `O` and
let `π` be an unramified generic constituent of `GL_(k+2)(F)` for `ψ` with characters `χ`
(the published `IsUnramifiedGenericConstituent`). If `π` is unitarizable, then
`|χ_i(ϖ)| < √q` for every `i`.

Proof.

1. Take a nonzero Whittaker functional `ℓ` (part of genericity). The published
   `unramifiedSphericalVector` (conjunct (A)) gives a normalized spherical test `w` in its
   model. As in the published proof of `sphericalTest_torus_eq_polynomial`, `w` is the
   coefficient function of a `GL_(k+2)(O)`-fixed vector `v`
   (`modelMap_surjective`, `mem_fixedVectors_of_model`).
2. `rowSum_bounded` gives `∑_{m<M} q^(k m) |ℓ(ρ(t_m) v)|² ≤ C`, with
   `t_m = diag(ϖ^m, 1, …, 1)`.
3. Worker 1767's published `UnramifiedWhittaker.sphericalTest_torus_schur` gives
   `ℓ(ρ(t_m) v) = halfModulus · satakeSchur = q^(-(k+1)m/2) h_m(a)`, with
   `a = characterValues F χ`.
4. So `q^(k m) |ℓ(ρ(t_m) v)|² = |u_m|²`, where `u_m = q^(-m/2) h_m(a)`. The partial sums
   of `|u_m|²` are bounded, so the series is summable (`summable_of_sum_range_le`) and
   `u_m → 0`.
5. By `hsymm_series_mul_prod` with `c = q^(-1/2)`, the series `∑ u_m t^m` is inverse to
   `∏ (1 - a_i q^(-1/2) t)`. So `norm_lt_one_of_mul_prod_eq_one` gives
   `|a_i q^(-1/2)| < 1`.
