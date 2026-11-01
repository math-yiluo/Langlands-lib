# The block Weyl cut correspondence

Authors: Worker 320 (Lean proof and first explanation) and Worker 913
(Markdown revision and submission).

`Langlands.Geometric.blockWeylCutStatement` proves exactly
`Langlands.Geometric.BlockWeylCutStatement`. The proof concerns the actual
`blockIndex`-preserving subgroups `blockWeyl B` of permutations of `Fin n` and
the published interior cuts `B.cuts` of ordered positive block shapes. It has
no extra hypotheses and makes no case distinction on the rank `n`.

## Block labels of a composition

The proof first compares the coordinate numbering of `BlockShape.ofComposition c`
with Mathlib's composition embedding. Induction on the prefix length identifies
the sum of the first `k` block sizes with `c.sizeUpTo k`. The explicit formula
for `finSigmaFinEquiv` then shows that coordinate `a` of block `i` of the
reconstructed shape is `c.embedding i a`. Applying `blockIndex_index` at the
composition's inverse embedding shows that the reconstructed shape's
`blockIndex` is exactly `c.index`.

## Boundaries and cut sides

For a boundary index `j`, a coordinate `a` lies strictly before
`c.boundary j` if and only if `c.index a` is strictly less than `j`. If the
block index is less than `j`, then `lt_sizeUpTo_index_succ` and monotonicity
of `sizeUpTo` place `a` before the boundary. If instead `j` is at most the block
index, `sizeUpTo_index_le` and monotonicity place `a` at or after it.
Consequently two coordinates have equal composition indices if and only if
every boundary places them on the same side.

The boundary positions `0` and `n` give constant truth values: no coordinate is
before `0` and every coordinate is before `n`. Every other boundary position is
`i.val + 1` for an actual interior cut `i`, by `BlockShape.mem_cuts_iff`, and
conversely every cut gives such a boundary. Since `a.val < i.val + 1` means
`a.val ≤ i.val`, surjectivity of the composition equivalence gives the general
law `blockIndex_eq_iff_cut_sides B a b`:

`blockIndex B a = blockIndex B b` if and only if, for every `i ∈ B.cuts`,
`a.val ≤ i.val ↔ b.val ≤ i.val`.

## The two clauses

For the adjacent coordinates `i.val` and `i.val + 1`, the only cut that can
separate them is `i`. The side law therefore identifies equal block labels
with absence of cut `i`. Evaluating a block-preserving swap at its left endpoint
gives equal labels. Conversely, the left, right and fixed-point formulas for a
swap show that equal labels suffice. This proves
`adjacent_swap_mem_blockWeyl_iff` directly from the subgroup definition.

For `blockWeyl_le_iff_cuts_subset`, subgroup inclusion forces each cut of the
coarser shape `B` to be a cut of the finer shape `K`: otherwise its adjacent
swap would lie in `blockWeyl K` by the first clause for `K`, but not in
`blockWeyl B` by the first clause for `B`. Conversely, a permutation preserving
the labels of `K` preserves the side of every cut of `K`, hence of every cut of
`B` under the assumed cut inclusion. The side law then shows that it preserves
the labels of `B`.

The final theorem packages the two clauses for every natural rank. At ranks
zero and one the type `Fin (n - 1)` of interior edges is empty, so the first
clause is vacuous; the general arguments cover these ranks without a separate
case. The endpoint cases in the boundary argument need no assumption of
distinct endpoints or positive rank.

## Provenance and dependencies

This proof is derived directly from the Library's block and cut definitions
and Mathlib's composition and finite-sum laws; it translates no external
literature theorem. Its sole project import is the statement module. It
introduces no representation-theoretic dependency and uses no classification
or exhaustion theorem. It supplies a finite combinatorial prerequisite, not an
alternating coefficient identity or the segment classification itself.
