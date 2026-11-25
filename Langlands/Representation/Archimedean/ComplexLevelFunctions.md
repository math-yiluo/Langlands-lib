# Level functions on `GL_n(ℂ)`

Building blocks of the principal-series functions used for the growth bound.

## Definitions

- `Tail n m`: the rows `m, …, n-1`, as the subtype `{j : Fin n // m ≤ j}`.
- `levelDet m A y = det (Y_m A)`, where `Y_m = tailRows m y` is the matrix of the rows
  `m, …, n-1` of `y` and `A` has `n` rows and columns indexed by `Tail n m`.
- `tailSelect m`: the column selection with `levelDet m (tailSelect m) 1 = 1`.
- `phase z = z / ‖z‖` for `z ∈ ℂˣ`.
- `levelChar m h b dτ a = |c|^{2 dτ - h - b} c^h c̄^b` with `c = ∏_{k ≥ m} a_k` (written with
  `normSq` and a complex power): the character of a level with `h` holomorphic and `b`
  antiholomorphic determinant factors and modulus increment `dτ`.

## Results

- `levelDet_mul`: `levelDet m A (y x) = levelDet m (x A) y`.
- `levelDet_upper_mul`, `levelDet_borel_mul`: left multiplication by an upper triangular `b`
  (in particular by `diag(a) u`, `u` upper unipotent) multiplies `levelDet m A` by
  `∏_{k ≥ m} b_kk`.
- `contDiff_levelDet`: `levelDet m A` is smooth on matrices.
- `conj_phase`, `eq_phase_mul_norm`, `norm_pow_eq_cpow`, `norm_cpow_two_mul`,
  `prod_cpow_ofReal_nonneg`, `prod_zpow_eq_zpow_sum'`, `prod_cpow_eq_cpow_sum`: elementary
  identities for phases, norms and complex powers.
- `levelChar_eq`: `levelChar m h b dτ a = ∏_{k ≥ m} phase(a_k)^{h - b} |a_k|^{2 dτ}`.
- `prod_tail_comm`: exchange of the products over levels `m` and positions `k ≥ m`.
- `prod_levelChar` (telescoping): if for every position `k` the sums over levels `m ≤ k` of
  `h_m - b_m` and of `dτ_m` are `l_k` and `τ_k`, then
  `∏_m levelChar m h_m b_m dτ_m a = ∏_k phase(a_k)^{l_k} |a_k|^{2 τ_k}`.

## Provenance

Internal infrastructure for the growth bound `ComplexLinkedSmallGrowthStatement`,
one of the two growth statements of the dimension-count route to
`ComplexLinkedLanglandsQuotientNotLargeStatement` in the Library module
`ComplexLinkedLanglandsQuotientGrowth`; see `ComplexLinkedSmallGrowthProof.md` for how the pieces
fit together. This route is an independent internal proof, not taken from the literature. The
module introduces no statement from the literature, and all its results are proved here.
