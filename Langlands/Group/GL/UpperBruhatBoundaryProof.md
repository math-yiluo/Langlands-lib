# Strict inversion decrease on boundaries of actual upper Bruhat cells: proof

Authors: Worker 913 (combinatorial comparison and final theorem), Worker 308
(conditional topological assembly), Worker 176 (reused rank-topology and
corner-continuity proofs).

`Langlands.GeneralLinear.upperBruhatBoundary.{u}` in
`Langlands.Group.GL.UpperBruhatBoundaryProof` proves exactly the published
proposition `Langlands.GeneralLinear.UpperBruhatBoundaryStatement.{u}` from
`Langlands.Group.GL.UpperBruhatBoundaryStatement`:

```text
∀ (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [T2Space K] (n : ℕ) (w : Equiv.Perm (Fin n)),
  closure (upperBruhatCell n K w) \ upperBruhatCell n K w ⊆
    {g | ∃ v : Equiv.Perm (Fin n),
      permutationInversionCount n v < permutationInversionCount n w ∧
      g ∈ upperBruhatCell n K v}
```

Every field universe, every Hausdorff topology making `K` a topological
division ring, every rank `n` including zero and every permutation are kept.
The closure is taken in the existing topology on the matrix units
`Langlands.GeneralLinear n K`. The theorem has no hypotheses. The target pair
and every imported pair are unchanged. The conclusion is only the stated
containment. The module does not prove equality with the union of shorter
cells, a closure-order characterization or a dimension formula.

The proof has two parts. A topological part reduces the statement to a finite
comparison of permutations. A combinatorial part proves that comparison.

## Published inputs

- `fieldUpperBruhatFactorizationTheorem` (`Langlands.Group.GL.UpperBruhatProof`)
  writes every `g` as `a * permutation n K v * b` with upper triangular `a, b`.
  With `mem_upperTriangularSubgroup_iff` this puts `g` in the actual cell
  `upperBruhatCell n K v`.
- `upperBruhatRankCharacterization` (`Langlands.Group.GL.UpperBruhatRankProof`,
  Worker 957) states that `g ∈ upperBruhatCell n K w` holds exactly when, for all
  `i j : Fin (n + 1)`, the zero-padded lower-left corner
  `UpperBruhatRank.corner i j g` has the same rank as the corresponding corner of
  `permutation n K w`. That corner keeps rows `r` with `i.val ≤ r.val` and
  columns `c` with `c.val < j.val`.
- `UpperBruhatRank.rank_corner_permutation` from the same module states that this
  permutation-corner rank is `UpperBruhatRank.count w i j.val`. That count is
  the number of columns `c` with `c.val < j.val` and `i.val ≤ (w c).val`.
- `permutationInversions`, `mem_permutationInversions_iff` and
  `permutationInversionCount_eq_card_permutationInversions`
  (`Langlands.Group.GL.UpperBruhatFiltration`) identify
  `permutationInversionCount n w` with the number of pairs `(p₁, p₂)` with
  `p₁ < p₂` and `w p₂ < w p₁`.

## Topological part (section `RankTopology` and `upperBruhatBoundary_of_rankOrder`)

The public lemmas `isOpen_matrix_rank_ge`, `isClosed_matrix_rank_le` and
`continuous_lowerLeftCorner` are imported from Worker 176's
`Langlands.Group.GL.UpperBruhatLocalClosednessProof`. Integration exposed the
existing declarations without changing their statements or proofs and removed
the duplicate copies from this module.

- **Rank at least `k` is open.** At a matrix `A` of rank at least `k`,
  `Matrix.exists_rank_normal_form` gives constant matrices `V`, `U` and a
  selection `f` of `k` indices with `(V * A * U).submatrix f f = 1`. The
  determinant of this minor is continuous in the matrix, so it is nonzero on an
  open neighbourhood of `A`. On that neighbourhood
  `Matrix.rank_of_det_ne_zero`, `Matrix.rank_submatrix_le` and
  `Matrix.rank_mul_le_left/right` give rank at least `k`.
- **Rank at most `k` is closed.** This set is the complement of rank at least
  `k + 1`.
- **The corners are continuous.** On the actual group, each entry of the padded
  corner is either the constant zero or an entry of `g`. The entry is continuous
  by `Units.continuous_val` and coordinate projections.

`rank_corner_le_of_mem_closure` proves the following. For `g` in the closure of
`upperBruhatCell n K w`, each corner rank of `g` is at most the corresponding
corner rank of `permutation n K w`. The set of `g` satisfying this bound is the
preimage of a closed rank bound under a continuous map, so it is closed. By the
rank characterization it contains the cell, so it contains the closure.

`upperBruhatBoundary_of_rankOrder` assumes the combinatorial implication
`horder`. Its hypotheses are `v ≠ w` and
`count v i j.val ≤ count w i j.val` for all `i j : Fin (n + 1)`, and its
conclusion is `permutationInversionCount n v < permutationInversionCount n w`.
Take `g ∈ closure (C_w) \ C_w`. The factorization theorem places `g` in some
`C_v`. Then `v ≠ w`, since `g ∉ C_w`. In `C_v` the rank characterization gives
equal corner ranks for `g` and `permutation n K v`. Combining this with the
closure bound and rewriting both permutation corners by
`rank_corner_permutation` gives `count v i j.val ≤ count w i j.val` for all
`i, j`. Then `horder` gives the strict inequality of inversion counts, and `v`
is the required witness.

## Combinatorial part (namespace `UpperBruhatBoundary`)

The section works with natural endpoints. `profile w i j` is the sum over
`c : Fin n` of `if c.val < j ∧ i ≤ (w c).val then 1 else 0`. By
`count_eq_profile`, `UpperBruhatRank.count w i k = profile w i.val k`. Below,
`inv` abbreviates `permutationInversionCount n`.

Two summation lemmas are used. `sum_add_one_le` states: if
`f c + (if c = a then 1 else 0) ≤ g c` for every `c`, then
`∑ f + 1 ≤ ∑ g`. `sum_comp_swap` states, for `a ≠ b`,

```text
∑ c, f c (v (swap a b c)) + f a (v a) + f b (v b)
  = ∑ c, f c (v c) + f a (v b) + f b (v a).
```

It is proved by splitting `a` and `b` off both sums.

**Effect of one swap.** Fix `a < b` with `v a < v b`. Then `v * swap a b` maps
`a ↦ v b` and `b ↦ v a`.

- `profile_mul_swap_le` states
  `profile (v * swap a b) i j ≤ profile v i j + 1` when
  `a < j ≤ b ∧ v a < i ≤ v b`, and
  `profile (v * swap a b) i j ≤ profile v i j` otherwise. It applies
  `sum_comp_swap` to the profile indicator, then splits on every indicator and
  finishes with `omega`.
- `permutationInversionCount_lt_mul_swap` states
  `inv v < inv (v * swap a b)`. Write `t = swap a b` and define
  `ψ p = (t p₁, t p₂)` if `t p₁ < t p₂`, and `ψ p = p` otherwise. The proof
  shows that `ψ` maps the inversions of `v` injectively into the inversions of
  `v * t` other than `(a, b)`, which is itself an inversion of `v * t`.
  - In the first case, `(t p₁, t p₂)` is an inversion of `v * t` because
    `t (t x) = x`. It is not `(a, b)`, because then `p = (b, a)`, which has the
    wrong order.
  - In the second case, `t` reverses the order of `p₁ < p₂`, so `p` meets
    `{a, b}`. Checking each position confirms that `p` is still an inversion
    of `v * t`, using `v a < v b`. It is not `(a, b)` because `v a < v b`.
  - Injectivity holds within each case because `t` is injective. Mixed cases
    contradict the case conditions.

  Then `Finset.card_le_card_of_injOn` and `Finset.card_erase_lt_of_mem` give the
  strict inequality.
- `permutationInversionCount_le` bounds the inversion count by `n * n`.

**One step towards `w`.** `exists_swap_step` states: if `v ≠ w` and
`profile v i j ≤ profile w i j` for all `i, j ≤ n`, then some `a < b` with
`v a < v b` satisfies `profile (v * swap a b) ≤ profile w` on the same range.

1. Let `a` be the least position with `v a ≠ w a`, so `v c = w c` for `c < a`.
2. Then `v a < w a`. If `w a < v a`, then `sum_add_one_le` at the corner
   `(v a, a + 1)` gives `profile w (v a) (a+1) + 1 ≤ profile v (v a) (a+1)`.
   This contradicts the hypothesis.
3. Let `b` be the least position `b > a` with `v a < v b ≤ w a`. This set is
   nonempty because it contains `v⁻¹ (w a)`. That position is not `a`, since
   `v a ≠ w a`. It is not below `a`, because there `v = w` and `w` is injective.
   By minimality, every `c` with `a < c < b` has `v c ≤ v a` or `w a < v c`.
4. Outside the rectangle `a < j ≤ b`, `v a < i ≤ v b`, `profile_mul_swap_le`
   and the hypothesis suffice. Inside it, `profile_add_one_le` proves
   `profile v i j + 1 ≤ profile w i j` as follows. `sum_add_one_le`, with the
   extra unit at `a`, gives

   ```text
   profile v i j + profile w (w a + 1) j + 1
     ≤ profile w i j + profile v (w a + 1) j.
   ```

   The pointwise check uses three facts: `v = w` below `a`; at `a`,
   `v a < i ≤ v b ≤ w a`; and between `a` and `b` the minimality alternative.
   The hypothesis at `(w a + 1, j)` then gives the claim. Its row endpoint
   `w a + 1` is at most `n`.

**Induction.** `inversionCount_lt_of_profile_le` uses strong induction on
`n * n - inv v`. Take a swap step from `v`. The inversion count strictly
increases. If the new permutation is `w`, the step proves the claim. Otherwise
the new permutation is still distinct from `w` with profile bounded by that of
`w`. Its value of `n * n - inv` is smaller, because `inv ≤ n * n`, so the
induction hypothesis applies. The empty rank `n = 0` needs no special
treatment: there `v ≠ w` is impossible.

`rankOrderInversion` restates this result with
`UpperBruhatRank.count v i j.val ≤ UpperBruhatRank.count w i j.val` for all
`i j : Fin (n + 1)`, through `count_eq_profile`. This is exactly the premise
of `upperBruhatBoundary_of_rankOrder`.

## Final theorem and provenance

```text
theorem upperBruhatBoundary : UpperBruhatBoundaryStatement.{u} :=
  upperBruhatBoundary_of_rankOrder UpperBruhatBoundary.rankOrderInversion
```

The development check reports only the axioms `propext`, `Classical.choice`
and `Quot.sound`.

This is an internal deduction from the published factorization theorem, the
published rank characterization and Mathlib. The combinatorial comparison was
written for this module. It is a form of the classical fact that the
lower-left rank comparison of permutations refines their inversion counts.
No literature proof route is claimed, and Shalika's Lemma 1.7(2), which
motivated the statement, is not used. No local compactness, countability,
dimension theory, cell coordinates or closed-orbit lemma is used.
