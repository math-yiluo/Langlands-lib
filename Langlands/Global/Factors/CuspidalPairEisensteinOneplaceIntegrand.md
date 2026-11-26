# The open-cell integrand on a cell at one unramified place

Module `Langlands.Global.Factors.CuspidalPairEisensteinOneplaceIntegrand`, namespace
`Langlands.Global.CuspidalPairEisenstein.Oneplace`.

The module proves the pointwise factorization of the open-cell integrand
`openCellIntegrand ψ φ s Y = W_M(φ_s)(w u'(Y)) conj(ψ_N(u'(Y)))` of
[CuspidalPairEisensteinPartialOpenCell.md](CuspidalPairEisensteinPartialOpenCell.md) on the
cells of the one-place decomposition of
[CuspidalPairEisensteinOpenCellExhaustion.md](CuspidalPairEisensteinOpenCellExhaustion.md).

## Content

- `fromBlocks_unipotent_mem`, `blockWeyl_mem_integralGroup` and
  `intertwiningUnipotent_mem_integralGroup`: over a `p`-adic field `K`, the block Weyl
  representative `w = blockWeyl (r+1) (t+1)` and the matrix `u'(Z)` of an integral matrix `Z`
  are integral (`Shahidi.UnramifiedSection.integralGroup`).
- `openCellUnipotent_add`: `u'(Y + Z) = u'(Y) u'(Z)` for adelic `Y`, `Z`.
- `comp_openCellWeyl`, `comp_openCellUnipotent`: the components at `v` of `w` and of `u'(Z)`
  are the local matrices `w` and `u'(Z_v)`, reindexed by `blockEquiv r t`.
- `openCellUnipotent_localMatrix`: `u'(localMatrix v y) = blockAt v (u'(y))`.
- `openCellIntegrand_eq`: the integrand is `W_M(φ_s)(w u'(Y)) conj(ψ(Y_(t,0)))`, by
  `openCellUnipotent_superdiagonal_sum`.
- `complex_localAdele`: `ψ(localAdele v x) = ψ_v(x)` for the canonical component `ψ_v` of `ψ`
  at `v` (`IsCanonicalFiniteAdditiveComponent`).
- **`openCellIntegrand_localMatrix_add`**: in the setting of `leviWhittaker_mul_blockAt`
  ([CuspidalPairEisensteinOneplaceLaw.md](CuspidalPairEisensteinOneplaceLaw.md)), for an
  adelic matrix `Z` integral at `v` and a local matrix `y ∈ M_((t+1)×(r+1))(F_v)`,

  `openCellIntegrand ψ φ s (localMatrix v y + Z) =
    f_v(w u'(y)) · conj(ψ_v(y_(t,0))) · openCellIntegrand ψ φ s Z`,

  where `f_v` is `Shahidi.UnramifiedSection.sectionFunction` for the Satake tuples `a` of `P`
  and `c` of `Pd` at `v`.

## Proof of `openCellIntegrand_localMatrix_add`

Let `k₀ = w u'(Z_v)`, an integral local matrix, and `g₀ = w u'(Z)`, whose component at `v` is
`k₀` (reindexed). Put `g' = g₀ · blockAt(v, k₀)⁻¹`; it has component `1` at `v`, and
`g₀ = g' · blockAt v k₀`.

- By `leviWhittaker_mul_blockAt`, `W_M(φ_s)(g₀) = f_v(k₀) W_M(φ_s)(g') = W_M(φ_s)(g')`, since
  `f_v` is `1` on integral matrices.
- `w u'(localMatrix v y + Z) = g₀ · blockAt v (u'(y)) = g' · blockAt v (k₀ u'(y))`, so
  `W_M(φ_s)(w u'(y_v + Z)) = f_v(k₀ u'(y)) W_M(φ_s)(g')`. The matrices `u'(Z_v)` and `u'(y)`
  commute, so `k₀ u'(y) = w u'(y) u'(Z_v)`, and `f_v(k₀ u'(y)) = f_v(w u'(y))` by right
  invariance of `f_v` under integral matrices.
- The character factor: `(y_v + Z)_(t,0) = localAdele v (y_(t,0)) + Z_(t,0)`, and
  `ψ(localAdele v x) = ψ_v(x)`.

## Provenance

This is the factorization `W(e) = W_v(e_v) · W^v(e^v)` of the Fourier coefficient at an
unramified place in the proof of Shahidi (1981), Theorem 5.1, p. 351
(`shahidi-1981-certain-l`), written for the integrand of the open-cell integral on the cells
`y_v + U_A`. The local factor `f_v(w u'(y)) conj(ψ_v(y_(t,0)))` is the summand of
`Shahidi.UnramifiedOpenCellSumStatement`.
