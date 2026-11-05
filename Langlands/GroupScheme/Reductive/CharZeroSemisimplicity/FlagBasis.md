# Bases adapted to a finite decreasing flag of subspaces

Author: Worker 1498.

This module contains pure linear algebra over a field `k`. It is an internal helper
for the proof of
`Langlands.GroupScheme.ReductiveCharZeroSemisimplicityStatement`, where it turns a
flag stable under a nilpotent family into block coordinates. A *flag* here is a
function `F : ℕ → Submodule k V` that is antitone and reaches `⊥` at some index
`m`.

## Declarations

- `exists_linearIndepOn_flag_step`: one downward step. Let `s` be a linearly
  independent set with a level function `e`, where every vector of `s` has level
  `≥ t + 1` and `F t' = span (s ∩ {e ≥ t'})` for all `t' ≥ t + 1`. Then there are
  a linearly independent `s'` and a level function `e'` with every level `≥ t` and
  `F t' = span (s' ∩ {e' ≥ t'})` for all `t' ≥ t`.
- `exists_linearIndepOn_flag`: for a flag with `F m = ⊥`, there are a linearly
  independent set `s ⊆ V` and a level function `e : V → ℕ` with
  `F t = span (s ∩ {v | t ≤ e v})` for every `t`.
- `exists_basis_flag`: if moreover `V = n → k` with `n` finite and `F 0 = ⊤`,
  there are a basis `b : Basis n k (n → k)` and levels `e : n → ℕ` with
  `F t = span (b '' {i | t ≤ e i})` for every `t`.
- `repr_apply_eq_zero_of_flag`: let `b` and `e` be adapted to `F` as above, and
  let `f` map every `F t` into `F (t + d)`. Then the coefficient
  `b.repr (f (b j)) i` vanishes whenever `e i < e j + d`.

## Proofs

`exists_linearIndepOn_flag_step`: the hypothesis at `t' = t + 1` gives
`F (t + 1) = span s`, so `s ⊆ F t` because the flag is antitone. Extend `s` to a
linearly independent `b ⊆ F t` spanning `F t`
(`exists_linearIndepOn_id_extension`). Keep the old levels on `s` and give the new
vectors level `t`. For `t' > t` the old vectors are exactly those of level `≥ t'`.
For `t' = t` every vector of `b` qualifies, and `span b = F t`.

`exists_linearIndepOn_flag`: induction on the distance `d` with `m ≤ t + d`,
starting from the empty set (all `F t'` with `t' ≥ m` are `⊥`). Each step uses
`exists_linearIndepOn_flag_step`. At `t = 0` this gives the claim for all `t`.

`exists_basis_flag`: since `F 0 = ⊤ = span s`, the set `s` is a basis
(`Basis.mk`). It is reindexed by `n` through `Basis.indexEquiv` with the standard
basis, and the levels move along the reindexing.

`repr_apply_eq_zero_of_flag`: `b j ∈ F (e j)`, so `f (b j) ∈ F (e j + d)`, which is
spanned by the basis vectors of level `≥ e j + d`. By `Basis.mem_span_image`, every
index in the support of `b.repr (f (b j))` has level `≥ e j + d`. So the
coefficient at `i` vanishes when `e i < e j + d`.
