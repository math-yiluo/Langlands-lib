# Lattice sums over rational row vectors with bounded denominators

Module `Langlands.Global.RankinSelberg.EqualAnalyticLattice`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

## Provenance

Internal. It reduces to the Library's lattice zeta sum
`Langlands.Global.Hecke.summable_one_add_norm_latticeVec_rpow`, which rests on Mathlib's
`ZLattice.summable_norm_rpow`.

## Declarations

- `exists_eq_algebraMap_of_integral`: an element of `F` integral at every finite place lies in `𝒪`
  (Mathlib `mem_integers_of_valuation_le_one`, as in the Library's `exists_int_trace_of_mem`).
- `IntegralRows F n D`: the rational row vectors `ξ ∈ F^n` with `D ξ_j ∈ 𝒪` for all `j`.
- `rowEmbedding F n ξ = (mixedEmbedding ξ_j)_j ∈ (F_∞)^n`.
- `mixedEmbedding_integer_eq_sum`: the mixed embedding of `a ∈ 𝒪` is
  `Σ_k (repr a k) • latticeBasis k`.
- `rowBasis F n`: the basis `Pi.single j (latticeBasis k)` of `(F_∞)^n`, with
  `rowBasis_latticeVec`.
- `summable_integralRows`: for nonzero `D` and `r > n [F : ℚ]`,
  `Σ_{ξ ∈ IntegralRows F n D} (1 + ‖rowEmbedding ξ‖)^(-r)` converges. Send `ξ` to the integer
  coordinates of `D ξ`. This map is injective. The comparison
  `1 + ‖D ξ‖ ≤ (1 + ‖D‖)(1 + ‖ξ‖)` reduces the sum to the Library's lattice sum.
