# Comparison of torus coordinates

Module: `Langlands.Global.SiegelFiniteness.Comparison`. Provenance: internal; real-variable
steps of the implemented proof of Siegel finiteness.

Let `x, x'` lie in the chamber with constant `K ≥ 0` (`Chamber K`: consecutive increases at
most `K`).

- `chamber_le`: `x_j ≤ x_i + nK` for `i ≤ j` (Library `sub_le_of_adjacent`).
- `sub_le_of_drops`: if every drop `x_p - x_q` (`q = p + 1`, `a < q ≤ b`) is at most `G ≥ 0`,
  then `x_a - x_b ≤ nG` (induction on `b - a`).
- `le_add_of_key` (**comparability**): if a relation `P` satisfies
  `P t j → x'_j ≤ x_t + β` and for every `i` some `P t j` holds with `j ≤ i ≤ t`, then
  `x'_i ≤ x_i + (β + 2nK)`: `x'_i ≤ x'_j + nK ≤ x_t + β + nK ≤ x_i + β + 2nK`.
- `not_of_drop` (**large drops**): if `x'_i ≤ x_i + Δ` for all `i`, `P t j → x_j ≤ x'_t + β`,
  and `x` drops by more than `Δ + β + 2nK` from `p` to `q = p + 1`, then `¬ P t j` whenever
  `t ≥ q > j`: otherwise `x_p ≤ x_j + nK ≤ x'_t + β + nK ≤ x_t + Δ + β + nK ≤
  x_q + Δ + β + 2nK`.
- `le_or_exists_drop`: if `x'_i ≤ x_i + Δ` and `G ≥ 0`, then for all `a, b` either
  `x'_a - x_b ≤ Δ + nK + nG`, or `x` drops by more than `G` at some `q` with `a < q ≤ b`
  (case `b ≤ a`: chamber and comparability; case `a < b` without such drops:
  `sub_le_of_drops`).
