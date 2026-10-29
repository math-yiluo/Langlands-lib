# Local closedness of actual upper Bruhat cells: proof

Author: Worker 176.

`Langlands.GeneralLinear.upperBruhatLocalClosedness.{u}` in
`Langlands.Group.GL.UpperBruhatLocalClosednessProof` proves exactly the existing
proposition `Langlands.GeneralLinear.UpperBruhatLocalClosednessStatement.{u}`:

```text
∀ (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [T2Space K] (n : ℕ) (w : Equiv.Perm (Fin n)),
  IsLocallyClosed (upperBruhatCell n K w)
```

The set is the actual upper triangular double coset in the existing group of
matrix units, with its existing topology. Every coefficient-field universe,
every coefficient topology satisfying these instances, every natural rank
including zero, and every permutation are retained.

## Open rank lower bounds

The private lemma `isOpen_matrix_rank_ge` proves that
`{A : Matrix (Fin n) (Fin n) K | k ≤ A.rank}` is open over a field with a
Hausdorff topological ring structure.

At a matrix `A` of rank at least `k`, Mathlib's
`Matrix.exists_rank_normal_form` supplies constant matrices `V`, `U` and an
equivalence `e` such that `V * A * U` is a block matrix with an identity block
of size `A.rank`. The map
`f a = e.symm (Sum.inl (Fin.castLE hA a))` selects `k` of these identity
coordinates. The proof checks entrywise that
`(V * A * U).submatrix f f = 1`.

The neighborhood

```text
{B | ((V * B * U).submatrix f f).det ≠ 0}
```

is open because the determinant, multiplication by constant matrices and
submatrix extraction are continuous, and a point is closed in a Hausdorff
space. It contains `A` since the selected determinant is one. On this
neighborhood `Matrix.rank_of_det_ne_zero` gives rank `k` for the selected
submatrix. The lemmas `Matrix.rank_submatrix_le`,
`Matrix.rank_mul_le_left` and `Matrix.rank_mul_le_right` bound that rank by
the rank of `B`. This proves the required neighborhood inclusion.

This argument also applies to `k = 0`, where the selected empty matrix has
determinant one. No positive-dimension assumption is used.

## Rank strata and finite profiles

`isClosed_matrix_rank_le` identifies rank at most `k` with the complement of
rank at least `k + 1`, so it is closed. The auxiliary
`isLocallyClosed_matrix_rank_eq` expresses a fixed-rank stratum as the
intersection of the open rank lower bound and the closed rank upper bound.

`isLocallyClosed_matrix_rank_profile` treats a finite family of continuous
matrix-valued maps `f i` on any topological space `X`, with prescribed natural
ranks `k i`. It explicitly writes

```text
{x | ∀ i, (f i x).rank = k i} =
  (⋂ i, (f i) ⁻¹' {A | k i ≤ A.rank}) ∩
  (⋂ i, (f i) ⁻¹' {A | A.rank ≤ k i}).
```

The first intersection is open by finiteness of the index type; the second
is closed. Rank equality is equivalent to the two inequalities, giving
Mathlib's `IsLocallyClosed` predicate directly.

## Continuous corners on the actual group

`continuous_lowerLeftCorner` proves continuity of the padded corner that
retains rows `r` with `i.val ≤ r.val` and columns `c` with `c.val < j.val`.
Each output entry is either a constant zero or an entry of the underlying
matrix. The latter is continuous by `Units.continuous_val` followed by two
coordinate projections. This uses the existing topology on matrix units.

The private lemma
`upperBruhatCell_isLocallyClosed_of_rank_characterization` applies the finite
profile lemma with index type `Fin (n + 1) × Fin (n + 1)`. The prescribed rank
at `(i,j)` is the rank of the same padded corner of `permutation n K w`.
Under its explicit rank-characterization premise, set extensionality and
`Prod.forall` identify the profile locus with `upperBruhatCell n K w`.

## Final theorem and provenance

The private helper `upperBruhatLocalClosedness_of_rank_characterization`
takes exactly `UpperBruhatRankCharacterizationStatement.{u}` and proves exactly
`UpperBruhatLocalClosednessStatement.{u}`. It introduces the latter's field,
topology, topological division ring, Hausdorff, dimension and permutation
quantifiers, then specializes the algebraic premise.

The final theorem discharges that premise with the published theorem
`Langlands.GeneralLinear.upperBruhatRankCharacterization` from
`Langlands.Group.GL.UpperBruhatRankProof`, authored by Worker 957. The final
theorem has no rank-characterization hypothesis. All imported pairs,
including the target statement pair, are unchanged.

This is an internal topological deduction from the published algebraic
characterization and Mathlib's matrix and topology results. It proves the
full internal generalization in the existing statement; it does not claim
to reproduce a literature proof. It requires no local compactness,
countability, orbit ordering or cell-coordinate theorem. Empty matrices and
empty corners are included. No manifold, dimension, boundary, filtration or
transpose conclusion is asserted.
