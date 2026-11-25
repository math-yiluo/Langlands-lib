# Test functions with prescribed holomorphic jets

For level data `(h, b, dτ)` and exponents `γ : Lw n → ℕ`:

## Definitions

- `selCol m k`: the selection of the columns `{k} ∪ {m+1, …, n-1}`.
- `gammaRow γ m k = γ_{(m, k)}` for `k < m` and `0` otherwise; `jRow γ m = Σ_k gammaRow γ m k`;
  `jExt` the same indexed by `ℕ`; `label γ m`: an enumeration of the column indices, `k` occurring
  `gammaRow γ m k` times (via `finSigmaFinEquiv`).
- `testMat`, `testFun γ h b dτ`: the level product with data `(h_m + J_m, b_m + J_m, dτ)`,
  `J_m = jRow γ m`, whose holomorphic factors at level `m` are `h_m` copies of
  `levelDet m (selCol m m)` and the `levelDet m (selCol m k)` (labels `k`), and whose
  antiholomorphic factors are `levelDet m (selCol m m)`.
- `testPoly γ = ∏_m ∏_k (nbH)_{mk}^{gammaRow γ m k}`.

## Results

- `levelDet_selCol`: for `k ≤ m`, `levelDet m (selCol m k) (nbMat v) = (nbMat v)_{mk}` (the
  matrix `rows_m(nbMat v) · selCol m k` is lower triangular with diagonal `(nbMat v)_{mk}, 1, …, 1`).
- `prod_label`, `detPart_testMat`, `gramExp_test`, `testFun_nbUnit`:
  `testFun (nbUnit v) = ∏_m T_m(v)^{σ_m - J_m} · ∏_m ∏_k (nbMat v)_{mk}^{γ_{mk}}` with
  `σ = gramExp h b dτ`.
- `testPoly_eq`: `testPoly γ = ∏_p X_p^{γ_p}`; `prod_lw`.
- `hasJet_testFun`: `testFun` has the jet `ιP (testPoly γ)` (with `N = Σ_m J_m` and
  `P = ∏_m gramF m^{N - J_m} · testPoly γ`).
- `testFun_mem_kFiniteFunctions`: if the level data telescope to `χ` as in
  `levelSpan_le_kFiniteFunctions`, `testFun` is a `U(n)`-finite principal-series function
  (the extra pairs do not change `h_m - b_m` or `dτ_m`).

## Provenance

Internal infrastructure for the proof of `ComplexStandardHolomorphicGrowthStatement`
(Library module `ComplexLinkedLanglandsQuotientGrowth`); see
`ComplexStandardHolomorphicGrowthProof.md` for the overall argument. The module introduces no
statement from the literature, and all its results are proved here.
