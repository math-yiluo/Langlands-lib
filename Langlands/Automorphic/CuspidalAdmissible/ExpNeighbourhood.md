# Exponential neighbourhoods of the identity

Module: `Langlands.Automorphic.CuspidalAdmissible.ExpNeighbourhood` (namespace
`Langlands.Global`). Provenance: internal.

- `expInf K n Z`: `exp Z` as an element of the infinite adelic group (via the archimedean
  one-parameter subgroup); `archimedeanGLCoordinates_expInf_val`: its coordinate matrix is
  `NormedSpace.exp Z`; `continuous_expInf`.
- `expBox K n δ L = {ofInfinite(exp Z) · ofFinite(l) : ‖Z‖ ≤ δ, l ∈ L}` and
  `continuous_expBoxMap`; `isCompact_expBox` for compact `L`.
- `expBox_mem_nhds`: for `δ > 0` and a neighbourhood `L` of `1`, `expBox δ L` is a
  neighbourhood of `1`. The inverse function theorem for `exp` at `0`
  (`hasStrictFDerivAt_exp_zero.map_nhds_eq_of_surj`) shows that `exp` of the open ball is a
  neighbourhood of `1` in the matrices; its preimage under the infinite coordinate map, meet the
  preimage of `L` under the finite projection, is contained in the box
  (`eq_ofInfinite_mul_ofFinite`).
