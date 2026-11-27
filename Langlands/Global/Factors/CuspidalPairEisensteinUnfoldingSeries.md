# The twisted section and the cell decomposition of the Eisenstein sum

Module `Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingSeries` (namespace
`Langlands.Global.CuspidalPairEisenstein`) collects the properties of the terms of the
cuspidal-pair Eisenstein sum `eisensteinSeries`
([CuspidalPairEisensteinSeries.md](CuspidalPairEisensteinSeries.md)) used in unfolding. It
also regroups the sum over the cells of
[CuspidalPairEisensteinUnfoldingCells.md](CuspidalPairEisensteinUnfoldingCells.md). Throughout,
`φ` satisfies `IsSection T T' φ` for cuspidal realizations `T`, `T'`, and `P = blockShape r t`.

## The twisted section

- `twisted φ s g = φ g · heightPower F r t s g` is the twisted section `φ_s = φ · H^s`. By
  definition `eisensteinSeries F φ s g = ∑' c, φ_s(γ_c g)` over `P(F) \ GL_N(F)` with chosen
  representatives `γ_c` (`eisensteinSeries_eq_tsum`).
- `continuous_of_isSection`: a section is continuous. This is the continuity part of
  `isAutomorphicFunctionOn_of_isSection` (module
  `Langlands.Global.Factors.CuspidalPairSchemeAutomorphy`).
- `continuous_heightPower`: `g ↦ H(g)^s` is continuous. By
  `heightPower_eq_schemeHeightPower` (module `Langlands.Global.Factors.CuspidalPairSchemeSeries`)
  it is the height power of the Iwasawa decomposition `isIwasawaCompact_blockParabolic`, which
  is continuous by `IsIwasawaCompact.continuous_heightPower`.
- `twisted_rational_mul`: `φ_s` is left invariant under `P(F)` (`isSection_rational_mul`,
  `heightPower_rational_mul`).
- `heightPower_unipotent_mul` and `twisted_unipotent_mul`: `H^s` and `φ_s` are left invariant
  under the unipotent radical `U(𝔸)`. The height is computed from a decomposition `g = q k` with
  `q` in the adelic parabolic and `k` in the standard compact subgroup (`heightPower_eq`), and
  the parabolic character is trivial on `U(𝔸)`.

## Invariance and continuity of the series

- `exists_out_mul`, `rightTranslate`, `tsum_out_mul_right`: for a subgroup `P` of a group `G`
  and a left `P`-invariant function, the sum over `P \ G` of its values at the representatives
  is unchanged by right translation of the representatives.
- `eisensteinSeries_rational_mul`: the series is left invariant under `GL_N(F)`.
- `NormalBound φ σ`: for every `s` with `σ < Re s` and every compact `C ⊆ GL_N(𝔸)`, the terms
  `‖φ_s(γ_c g)‖` with `g ∈ C` are bounded by one summable function of `c`.
  `exists_normalBound`: some `σ` has this property. This is the normal convergence theorem
  `exists_summable_eisensteinTerm_bound` (module
  `Langlands.Global.Factors.CuspidalPairEisensteinConvergence`), applied with a single `s`.
- `summable_norm_twisted`, `continuous_eisensteinSeries`: on `Re s > σ` the series converges
  absolutely, and it is continuous by the Weierstrass M-test on compact neighbourhoods.

## The sum over the cells

- `cellTerm φ s J q g = φ_s(γ_J δ_q g)` is the term at the coset `P(F) γ_J δ_q`, where `δ_q`
  represents `q ∈ Λ_J(F) \ N₀(F)`. `cellTerm_eq`: it equals the term of the series at the
  image of `(J, q)` under the bijection `cellOrbitMap_bijective`, by `P(F)`-invariance.
- `summable_norm_cellTerm_sigma`: over `Σ J, Λ_J(F) \ N₀(F)` the norms are summable, with the
  same total as `∑' c, ‖φ_s(γ_c g)‖`. `cellTerm_fiber_le`: the sum over one cell is summable and
  bounded by that total.
- `eisensteinSeries_eq_sum_cells`: for `σ < Re s`, `E(φ, s)(g) = ∑_J ∑'_q cellTerm φ s J q g`, a
  finite sum over the subsets `J` of size `t + 1`. This is the two-block `GL_N` analogue of the
  regrouping of the Eisenstein sum by double cosets in Shahidi, *Functional equation satisfied by
  certain L-functions*, Compositio Math. 37 (1978), proof of Lemma 2.1, (2.10.2)–(2.10.3), pp.
  181–182. The source sums over the right quotient `G_F/P_F` and indexes the double cosets by the
  classes `w ∈ W/W_M`. Here the sum is over the left quotient `P(F) \ GL_N(F)`, which corresponds to
  it under inversion `g ↦ g⁻¹`, and the double cosets are indexed by the pivot sets `J`.
- `exists_bound_unipotent` (**uniform bound on `N₀(𝔸)`**): there is `B` with
  `∑' c, ‖φ_s(γ_c n)‖ ≤ B` for all `n ∈ N₀(𝔸)`. A compact set `K` meets every `N₀(F)`-orbit
  (`exists_isCompact_pattern_cover` with `J = ∅`). The normal bound on `K`, together with the
  invariance of the sum of norms under right translation of the representatives by `GL_N(F)`,
  gives the bound everywhere. This bound justifies interchanging the sums and the integral over
  `N₀(F) \ N₀(𝔸)` in the unfolding.
