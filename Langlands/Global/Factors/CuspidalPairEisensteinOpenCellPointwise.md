# A pointwise majorant for the open-cell integrand

Module `Langlands.Global.Factors.CuspidalPairEisensteinOpenCellPointwise`, namespace
`Langlands.Global.CuspidalPairEisenstein.OpenCellPointwise`.

The module bounds the open-cell integrand `openCellIntegrand ψ φ s` of
[CuspidalPairEisensteinPartialOpenCell.md](CuspidalPairEisensteinPartialOpenCell.md) by a
constant multiple of the majorant `Ω_e` of
[CuspidalPairEisensteinOpenCellMajorant.md](CuspidalPairEisensteinOpenCellMajorant.md), with
`e = Re s + b` for a real `b` depending only on `φ`, for every `s` with `e = Re s + b ≥ 0`
(the determinant comparison it uses holds only for nonnegative exponents). Here `N = r + t + 2`, `|det|` is `absDet`,
and `m = diag(m₁, m₂)` is the Levi part of `p` in a factorization `w u'(Y) = p k` with `p` in the
upper parabolic `P` of block sizes `(r + 1, t + 1)` and `k` in the standard maximal compact
subgroup.

## Content

- `absDet_one`, `absDet_pow`.
- `absDet_openCellWeyl`: `|det w|_𝔸 = 1`.
- `det_val_reindex`, `det_openCellUnipotent` (`det u'(Y) = 1`), `absDet_eq_one_of_det_eq_one`,
  `absDet_openCellUnipotent`.
- `absDet_of_mem_standardCompact`: `|det k|_𝔸 = 1` for `k` in the standard maximal compact
  subgroup.
- `absDet_parabolic`: `|det p|_𝔸 = |det m₁|_𝔸 |det m₂|_𝔸`.
- **`absDet_leviFst_mul_leviSnd`**: if `p k = w u'(Y)` with `k` in the standard maximal compact
  subgroup, then `|det m₁|_𝔸 |det m₂|_𝔸 = 1`.
- **`norm_levFactor_mul_pairWeight`**: if `|det m₁|_𝔸 |det m₂|_𝔸 = 1`, then
  `|levFactor s m| · |det m₁|^(β₁) |det m₂|^(β₂) = |det m₂|_𝔸^(-(Re s + N/2 + β₁ - β₂))`, where
  `Oneplace.levFactor s m = δ_P(m)^(1/2) exp((s/N) log δ_P(m))`.
- **`exists_norm_openCellIntegrand_le`**: for a standard additive character `ψ` and a section
  `φ` with `IsSection T T' φ` (with `[CompactSpace (AdeleQuotient F)]`) there is `b ∈ ℝ` such
  that for every `s` with `Re s + b ≥ 0` there is `C ≥ 0` with
  `|openCellIntegrand ψ φ s Y| ≤ C · Ω_(Re s + b)(Y)` for all `Y`.

## Proofs

- `absDet_openCellWeyl`: `w` is the image of a permutation `σ` under the homomorphism
  `GeneralLinear.permutation` followed by a reindexing, so `w^(ord σ) = 1`; hence
  `|det w|^(ord σ) = 1` and `|det w| = 1` since it is positive.
- `det_openCellUnipotent`: after the reindexings (`Matrix.det_reindex_self`), `u'(Y)` is the
  block matrix `[[I, Y], [0, I]]` (`Shahidi.upper`), whose determinant is `1`
  (`Matrix.det_fromBlocks_zero₂₁`).
- `absDet_of_mem_standardCompact`: a continuous homomorphism to `ℝ≥0ˣ` is trivial on a compact
  subgroup (`RankinSelberg.LastRowReduction.eq_one_of_isCompact`).
- `absDet_parabolic`: `GeneralLinear.determinant_blockParabolic` and multiplicativity of the
  idelic absolute value; the product over the two blocks is `prod_blocks`.
- `absDet_leviFst_mul_leviSnd`: take `|det|` of `p k = w u'(Y)`.
- `norm_levFactor_mul_pairWeight`: with `X = |det m₂|` and `L = log X`, `|det m₁| = e^(-L)` and
  `δ_P(m) = |det m₁|^(t+1) / |det m₂|^(r+1) = e^(-N L)` (`Oneplace.leviCharacter_leviOf`), so
  `|levFactor s m| = e^(-N L / 2) e^(-Re(s) L)` (`coe_leviHalfCharacter`, `Complex.norm_exp`) and
  the product is `e^(-(Re s + N/2 + β₁ - β₂) L)`.
- `exists_norm_openCellIntegrand_le`: take `β₁`, `β₂`, `C` from
  `OpenCellBound.exists_slice_bound` and `b = N/2 + β₁ - β₂`. For `Y`, factor
  `w u'(Y) = p k` (`Oneplace.exists_parabolic_factor'`). Since `|ψ| = 1`, the integrand has
  absolute value `|W_M(φ_s)(p k)|`, which is at most
  `|levFactor s m| C |det m₁|^(β₁) |det m₂|^(β₂)` by `OpenCellBound.norm_leviWhittaker_le`, that
  is `C |det m₂|^(-(Re s + b))` by the two previous results, and
  `OpenCellDeterminant.rpow_neg_absDet_le_majorant` bounds this by
  `C ((t + 2)!^d)^e 2^e Ω_e(Y)` with `e = Re s + b ≥ 0` and `d = [F : ℚ]`.

## Provenance

Shahidi, *On certain L-functions*, Amer. J. Math. 103 (1981) (`shahidi-1981-certain-l`), proof
of Theorem 5.1, p. 352: the local components are "dominated by the corresponding intertwining
integral". The bound here is a global analogue of this domination. With `g = w u'(Y) = p k` and
`m = diag(m₁, m₂)`, it reads
`|W_M(φ_s)(g)| ≤ C |δ_P(m)^(1/2 + s/N)| · |det m₁|^(β₁) |det m₂|^(β₂)`, where the determinant
powers account for the growth of the cusp forms (no unitarity of central characters is used);
on the open cell `|det m₁| |det m₂| = 1`, and when `e = Re s + b ≥ 0` the determinant bound
turns the right side into a multiple of `Ω_e`. The exponent bookkeeping and the comparison with `Ω_e` are internal to the
formal proof.
