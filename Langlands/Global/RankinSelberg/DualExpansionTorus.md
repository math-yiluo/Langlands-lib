# Torus integrals: orthogonality, Fubini, reindexing and series

Module `Langlands.Global.RankinSelberg.DualExpansionTorus`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`. It extends the Library's torus integrals
`Langlands.Automorphic.CuspidalWhittaker.torusIntegral` (normalized integrals over
`(𝔸 / F)^ι` of periodic functions).

Provenance: internal.

- `pairChar ψ a y = ψ(Σ_i a_i y_i)` for rational `a`; `torusIntegral_pairChar` is the
  orthogonality relation: its torus integral is `1` if `a = 0` and `0` otherwise, for a
  character `ψ` trivial on `F` such that for every `a ≠ 0` in `F` some `y` has
  `ψ(a y) ≠ 1`.
- `torusIntegral_of_isEmpty`: over an empty index type the torus integral is evaluation at `0`.
- `torusIntegral_sum_elim`: Fubini over a sum of index types `α ⊕ β`.
- `torusIntegral_reindex`: invariance under reindexing along an equivalence (`reindexHom`).
- `norm_torusIntegral_le`: a uniform bound on the integrand bounds the integral.
- `torusIntegral_tsum`: a series of continuous periodic functions with a uniform bound on the
  sum of norms can be integrated termwise. `sum_norm_torusIntegral_le` bounds finite sums of the
  norms of the termwise integrals by the same bound.
