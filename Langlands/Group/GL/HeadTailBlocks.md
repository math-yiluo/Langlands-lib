# First-block and tail standard coordinates

Author: Worker 121.

This module constructs the first-block/tail grouping of an ordered positive
`B : GeneralLinear.BlockShape n`. Its indexing parameter is
`h : B.length = k + 2`, where `k : ℕ`; thus the tail has `k + 1` blocks and
is nonempty. All declarations are in `Langlands.GeneralLinear.BlockShape`.

## Shapes and labels

`headIndex B h` is `Fin.cast h.symm 0` and `tailIndex B h j` is
`Fin.cast h.symm j.succ`. `headRank B h` is the size of the first block,
and `tailRank B h` is the sum of the sizes at all tail labels. Both ranks
are positive, and `headRank_add_tailRank` proves their sum is `n`.
`tailRank_eq_sub` gives the equivalent subtraction formula.

`headShape B h` is the single-block shape of rank `headRank B h`.
`tailShape B h` has precisely the `k + 1` remaining ordered sizes.
`headTailShape B h` has two blocks, of sizes head rank and tail rank:
it first constructs the shape of their sum and then uses the published
`rankCast` with the proved rank equality. The length and size projection
formulas are exported as simplification lemmas.

`headTailRefinement B h` is definitionally a
`Geometric.BlockRefinement (headTailShape B h)`. Its declared dependent
function type explicitly exposes the two outer ranks, to ease elaboration
with `Fin 2`. At outer label zero it is exactly `headShape B h`, and at
outer label one it is exactly `tailShape B h`; the corresponding equalities
are `headTailRefinement_zero` and `headTailRefinement_one`.
`headTailRefinement_total_length` and `headTailRefinement_total_rank`
compute the total number of nested blocks and the sum of their sizes.

`headTailBlockEquiv B h` maps the nested labels
`(i : Fin 2) × Fin (headTailRefinement B h i).length` bijectively to
`Fin B.length`. Its inverse gives the reverse correspondence requested by
consumers. It uses consecutive `finSigmaFinEquiv` numbering followed by
the proved equality of block counts. `headTailBlockEquiv_head` sends the
sole head label to `headIndex`, and `headTailBlockEquiv_tail` sends each
tail label to `tailIndex`. `headTailBlock_size` proves equality of every
corresponding size, so these are the original ordered sizes, with no
permutation or rank-cast hypothesis supplied by the caller.

`tailIndex_strictMono` and `headIndex_lt_tailIndex` describe the original
label order. `headTailBlock_lt_of_outer_lt` and
`headTailBlock_strictMono` give the two corresponding nested order laws:
earlier outer blocks precede later ones, and each inner block list retains
its order. Together these describe the ordered flattening.

## Exact consecutive coordinates

`head_index_val` says the first original block starts at zero.
`tail_index_val` says each original tail coordinate has value equal to
head rank plus its coordinate in `tailShape`. The proof expands standard
numbering using `finSigmaFinEquiv_apply` and separates the first summand
with `Fin.sum_univ_succ`.

`headTailShape_index_zero` and `headTailShape_index_one` give the same
two offsets for the outer shape. Combining these formulas with the
published single-block coordinate identity proves `headTail_index`:

```text
(headTailShape B h).index i ((headTailRefinement B h i).index j x)
  = B.index (headTailBlockEquiv B h ⟨i,j⟩)
      (Fin.cast (headTailBlock_size B h ⟨i,j⟩) x).
```

The cast changes only the type of the inner coordinate. Its value is
unchanged. A private congruence lemma handles the equal original labels
and equal coordinate values without assuming any matrix reindexing identity.

## Actual groups and topology

The following constructions work for every `R : Type u` with `CommRing R`,
in an independent universe, including rings with zero equal to one.

| Declaration | Result |
| --- | --- |
| `headTailNestedLeviEquiv B h R` | Multiplicative equivalence from `B.Levi R` to the product of the head and tail inner Levi products. |
| `headTailNestedLeviEquiv_entry` | Each nested matrix entry is the entry of the corresponding original block, with both coordinates cast by `headTailBlock_size`. |
| `headTailNestedLeviEquiv_symm_apply` | The inverse component formula uses `GeneralLinear.reindex` with `finCongr headTailBlock_size`, the opposite direction to the forward map. |
| `headTailLeviEquiv B h R` | Multiplicative equivalence from `B.Levi R` to the actual `Geometric.refinedLevi R (headTailShape B h) (headTailRefinement B h)`. |
| `headTailLeviEquiv_val` | Each outer component is the actual inner block diagonal embedding of the nested Levi components. |
| `headTailLeviEquiv_embedding` | Its outer block diagonal embedding is exactly `B.leviEmbedding R`, as an equality of ambient matrices. |
| `headTail_composedParabolic_eq` | The actual composed upper parabolic equals `B.parabolic R` as a subgroup of `GeneralLinear n R`. |
| `headTailParabolicEquiv B h R` | The resulting multiplicative equivalence of parabolic subtype presentations; `headTailParabolicEquiv_val` shows that it retains the underlying matrix. |
| `headTail_composedLeviProjection` | The composed projection after the parabolic equivalence equals `headTailLeviEquiv` after `B.leviProjection R`. |

For `TopologicalSpace R` and `IsTopologicalRing R`, the suffix
`Continuous` on each of `headTailNestedLeviEquiv`, `headTailLeviEquiv`,
and `headTailParabolicEquiv` supplies the same multiplicative equivalence
with continuity in both directions, for the actual product and subgroup
topologies.

These declarations specialize the published `RefinementCoordinates`
construction to the explicit label equivalence, size equality, and
coordinate identity proved here. In particular, the actual Levi map
uses `Geometric.refinedLeviEquiv`, and the continuous version uses
`Geometric.refinedLeviEquivContinuous` through that construction. The
subgroup equality and projection comparison follow from its actual
upper-parabolic/preimage argument; neither is an extra assumption.

## Provenance and scope

This is an internal derivation from the published definitions in
`Group.GL.Blocks`, `Group.GL.SingleBlock`,
`Representation.Geometric.RefinementDefinitions`,
`Representation.Parabolic.RefinementComposition`, and the proved bridge
in `Group.GL.RefinementCoordinates`, together with Mathlib's finite
consecutive numbering and finite sums. It does not claim to transcribe a
new theorem from the original literature. The rank transport, nested
subgroup equivalence, and generic coordinate bridge are reused by import.

The module constructs geometry and its structural identities only. It
contains no modulus factorization, induced-function equivalence, external
tensor split, adjacent-merge construction, or representation-theoretic
transitivity theorem.
