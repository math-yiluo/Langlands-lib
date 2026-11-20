# Equivalent strata: order, depth and level

Helper module for the proof of `Langlands.BushnellKutzko.StratumEquivalenceStatement`
(Bushnell–Kutzko 1993, (1.5.2), printed p. 43). All results are about lattice chains
`𝓛` over the integers `𝒪[F]` of a nonarchimedean local field `F`, with filtration
`𝔓^n = 𝓛.endFiltration n`, and use the published `radicalFiltration`.

- `endFiltration_mul_eq`: `𝔓^m 𝔓^n = 𝔓^{m+n}` (item 1 of `radicalFiltration`).
- `mem_endFiltration_iff_mul`: `x ∈ 𝔓^m` iff `x 𝔓^n ⊆ 𝔓^{m+n}`. The forward direction is
  the product rule; conversely `1 ∈ 𝔓^0 = 𝔓^n 𝔓^{-n}`, so `x = x·1 ∈ 𝔓^{m+n} 𝔓^{-n} ⊆ 𝔓^m`.
- `endFiltration_zero_eq`: if `𝔓₁^a = 𝔓₂^c` then `𝔓₁^0 = 𝔓₂^0` (apply the colon
  description with `m = 0`).
- `mem_endFiltration_one_iff`, `endFiltration_one_eq`: `𝔓^1` is the Jacobson radical of the
  order (item 4 of `radicalFiltration`), so chains with the same order have the same `𝔓^1`.
- `endFiltration_eq_of_eq`: if `𝔓₁^a = 𝔓₂^c` then `𝔓₁^k = 𝔓₂^k` for all `k`: for `k ≥ 0` by
  induction using `𝔓^{k+1} = 𝔓^k 𝔓^1`, for `k < 0` by the colon description
  `𝔓^k = {x : x 𝔓^{-k} ⊆ 𝔓^0}`.
- `endFiltration_injective`: `n ↦ 𝔓^n` is injective: if `𝔓^a = 𝔓^c` with `a < c` then
  `𝔓^0 = 𝔓^{c-a} ⊆ 𝔓^1`, so `1 ∈ 𝔓^1`, whence `L_0 ⊆ L_1`, contradicting `L_1 ⊊ L_0`.
- `endFiltration_neg_r_eq`: equivalent strata (equal cosets `b + 𝔓^{-r}`) have the same
  lattice `𝔓^{-r}`; `sub_mem_of_equivalent`: `b_S - b_T ∈ 𝔓_T^{-r_T}`.
- `endFiltration_eq_of_equivalent`, `order_eq_of_equivalent`, `r_eq_of_equivalent`:
  equivalent strata have the same filtration, hence the same order and (by injectivity)
  the same `r`.
- `mem_of_valuation_eq`: if `v_𝔄(x) = m` then `x ∈ 𝔓^m` and `m` is the largest such index
  (item 5 of `radicalFiltration` makes the defining supremum a maximum).
- `le_of_valuation_eq`, `n_eq_of_equivalent`: if `v_𝔄(b_S) = -n_S` and `v_𝔄(b_T) = -n_T`,
  then `b_T = b_S - (b_S - b_T) ∈ 𝔓^{-n_S}` since `-r > -n_S`, so `n_T ≤ n_S`; by
  symmetry `n_S = n_T`.

BK93 prints a short proof under (1.5.2), p. 43. Equivalence gives `𝔓₁^{-r₁} = 𝔓₂^{-r₂}`.
Since `𝔓` is an invertible fractional ideal of `𝔄` (`𝔓^m 𝔓^{-m} = 𝔄`), each order is
recovered as `𝔄 = {x : x 𝔓^m ⊆ 𝔓^m}`. Hence the orders agree, and so do the radicals and
`r`, from which the exact-level assertion follows. The Lean argument is the same:
`mem_endFiltration_iff_mul` is the colon description, proved from `1 ∈ 𝔓^n 𝔓^{-n}`.
`endFiltration_one_eq` and `endFiltration_injective` supply the radical and `r`, and
`n_eq_of_equivalent` gives the level.
