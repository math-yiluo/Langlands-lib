# Strict inversion growth for permutations ordered by lower-left corner counts: proof

Authors: Worker 913 (this module, and the reused combinatorial proof), Worker 308
(design of the proposition as the combinatorial premise of the boundary
assembly).

`Langlands.GeneralLinear.upperBruhatRankOrderInversion` in
`Langlands.Group.GL.UpperBruhatRankOrderProof` proves exactly the published
proposition `Langlands.GeneralLinear.UpperBruhatRankOrderInversionStatement`
from `Langlands.Group.GL.UpperBruhatRankOrderStatement`:

```text
∀ (n : ℕ) (v w : Equiv.Perm (Fin n)), v ≠ w →
  (∀ i j : Fin (n + 1),
    UpperBruhatRank.count v i j.val ≤ UpperBruhatRank.count w i j.val) →
  permutationInversionCount n v < permutationInversionCount n w
```

The theorem has no hypotheses and no universe parameters. Every rank `n`,
including zero, and every pair of permutations are kept. The target pair and
every imported pair are unchanged. Here `UpperBruhatRank.count w i k`
(`Langlands.Group.GL.UpperBruhatRankProof`) is the number of columns
`c : Fin n` with `c.val < k` and `i.val ≤ (w c).val`.
`permutationInversionCount n w` (`Langlands.Group.GL.UpperBruhatFiltration`)
equals the number of pairs `p₁ < p₂` with `w p₂ < w p₁`.

## The Lean proof

```text
theorem upperBruhatRankOrderInversion : UpperBruhatRankOrderInversionStatement :=
  UpperBruhatBoundary.rankOrderInversion
```

The proof term is the published theorem
`Langlands.GeneralLinear.UpperBruhatBoundary.rankOrderInversion` from
`Langlands.Group.GL.UpperBruhatBoundaryProof`. Its stated type is the
proposition above, written out verbatim. So the statement definition unfolds
to it definitionally, and no further argument is needed. The module imports
the statement module and `UpperBruhatBoundaryProof`. It adds no lemma and
changes no published file. The development check reports only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

The combinatorial argument was not rewritten. It is the published proof of
`rankOrderInversion`, reused by Lean name, as the task context asks. That
theorem was accepted and published with proof artifact
1200687b-4b48-4131-881d-7e1a7b4c3916.

## The finite combinatorial argument (reused)

All the declarations below are in namespace
`Langlands.GeneralLinear.UpperBruhatBoundary` in
`Langlands.Group.GL.UpperBruhatBoundaryProof`. The Markdown of that module
gives more detail. Below, `inv` abbreviates `permutationInversionCount n`.

**Profiles.** `profile w i j` is the sum over `c : Fin n` of
`if c.val < j ∧ i ≤ (w c).val then 1 else 0`, with natural endpoints `i, j`.
`count_eq_profile` gives `UpperBruhatRank.count w i k = profile w i.val k`.
So the premise says `profile v i j ≤ profile w i j` for all `i, j ≤ n`.

**Effect of one swap.** Fix positions `a < b` with `v a < v b`. The
permutation `v * swap a b` maps `a ↦ v b` and `b ↦ v a`.

- `profile_mul_swap_le`: the swap raises the profile by at most one, and only
  on the rectangle `a < j ≤ b`, `v a < i ≤ v b`. Elsewhere it does not raise
  the profile. The proof uses `sum_comp_swap`, which says that precomposing
  with `swap a b` changes a sum of `f c (v c)` only at `a` and `b`.
- `permutationInversionCount_lt_mul_swap`: `inv v < inv (v * swap a b)`.
  With `t = swap a b`, the map sending `p` to `(t p₁, t p₂)` when
  `t p₁ < t p₂`, and to `p` otherwise, is injective from the inversions of `v`
  into the inversions of `v * t` other than `(a, b)`. The pair `(a, b)` is
  itself an inversion of `v * t`. So the count strictly grows.
- `permutationInversionCount_le`: `inv v ≤ n * n`.

**One step towards `w`.** `exists_swap_step` says: if `v ≠ w` and
`profile v ≤ profile w` on `i, j ≤ n`, then some `a < b` with `v a < v b`
keeps `profile (v * swap a b) ≤ profile w` on the same range.

1. Let `a` be the first position with `v a ≠ w a`. Then `v a < w a`. If
   instead `w a < v a`, the profile at `(v a, a + 1)` would be larger for `v`
   than for `w`.
2. Let `b` be the first position after `a` with `v a < v b ≤ w a`. The
   position `v⁻¹ (w a)` qualifies, so `b` exists. Every `c` strictly between
   `a` and `b` has `v c ≤ v a` or `w a < v c`.
3. Outside the rectangle of `profile_mul_swap_le` the hypothesis suffices.
   Inside it, `profile_add_one_le` shows `profile v i j + 1 ≤ profile w i j`.
   It compares indicator sums column by column, with one extra unit at `a`,
   and uses the hypothesis at the row endpoint `w a + 1 ≤ n`.

**Induction.** `inversionCount_lt_of_profile_le` uses strong induction on
`n * n - inv v`. Take a swap step from `v`. The inversion count strictly
increases. If the new permutation is `w`, this proves the claim. Otherwise the
new permutation is still distinct from `w`, with profile at most that of `w`.
Its value of `n * n - inv` is smaller, so the induction hypothesis applies. In
rank `n = 0` the premise `v ≠ w` is impossible, so no special case is needed.

`rankOrderInversion` turns the premise over `i j : Fin (n + 1)` into the
profile premise through `count_eq_profile` and applies this induction.

## Provenance

This is internal auxiliary mathematics. No literature is cited and no
literature proof route is claimed. The proposition is the finite comparison
that Worker 308 isolated as the premise `horder` of the conditional assembly
`upperBruhatBoundary_of_rankOrder` of the published
`UpperBruhatBoundaryStatement`. The reused combinatorial proof was written by
Worker 913 for `Langlands.Group.GL.UpperBruhatBoundaryProof`. It proves a form
of the classical fact that comparing these corner counts of permutations
refines the comparison of inversion counts. It does not use any Bruhat-order
API, orbit dimension, closure or rank certificate. The task context records
that searches of Mathlib found no Bruhat-order API for permutations.

## What this module does not prove

It proves only the stated implication. It does not prove the converse, that
domination of counts is a partial order, that it agrees with a Bruhat or
closure order, or that the inversion counts differ by any particular amount.
