# Literal two-grouping geometry for three positive blocks

Author: Worker 838.

This internal module collects, at the single total rank `C + (A + B)`, the
ordered refinement data that the proposition
`Parabolic.OrderedProductRegrouping` needs for both bracketings of three
consecutive blocks of positive ranks `C`, `A`, `B`. It is block-shape
bookkeeping only: it constructs no representation and does not assume or prove
a regrouping theorem or three-block associativity.

The module does not rebuild any geometry. The three-block shape and the data of
the bracketing `C, (A, B)` are the published declarations of
[`ThreeBlockRefinementGeometry`](../../Representation/Parabolic/ThreeBlockRefinementGeometry.md).
That module states the bracketing `(C, A), B` for the outer shape
`twoBlocks (C + A) B` at total rank `(C + A) + B`, against `threeBlocksRight`.
This module adds the same bracketing for the outer shape
`(twoBlocks (C + A) B).rankCast (Nat.add_assoc C A B)` at total rank
`C + (A + B)`, against `threeBlocks` itself. It also adds the specialization,
length, size and label-value laws below as named lemmas.

All declarations are in namespace `Langlands.Parabolic`. They take the explicit
natural numbers `C A B` and the positivity hypotheses `hC : 0 < C`,
`hA : 0 < A`, `hB : 0 < B`, in this order.

## The three-block shape

The shape is the published `threeBlocks C A B hC hA hB : BlockShape (C + (A + B))`.

- `threeBlocks_length`: its length is `3`.
- `threeBlocks_size`: its sizes are `![C, A, B]`.

## The bracketing `C, (A, B)`

The outer shape is `twoBlocks C (A + B) hC (Nat.add_pos_left hA B)`. The data
are the published `leftRefinement`, `leftLabelEquiv`, `leftLabelEquiv_size` and
`leftLabelEquiv_index`. The last is the exact coordinate identity
`(twoBlocks C (A + B) …).index j ((leftRefinement … j).index k x) =
(threeBlocks …).index (leftLabelEquiv … ⟨j, k⟩) (Fin.cast (leftLabelEquiv_size … ⟨j, k⟩) x)`.
This module adds:

- `leftRefinement_zero`: `leftRefinement … 0` is
  `CuspidalSupport.LeviAdmissibility.oneBlock C hC`, the one-block shape of rank
  `C`.
- `leftRefinement_one`: `leftRefinement … 1` is `twoBlocks A B hA hB`.
- `leftRefinement_length_zero`, `leftRefinement_length_one`: the inner lengths
  are `1` and `2`.
- `leftRefinement_size_zero`, `leftRefinement_size_one`: the inner sizes are
  `fun _ => C` and `![A, B]`.
- `leftLabelEquiv_apply_zero_zero`, `leftLabelEquiv_apply_one_zero`,
  `leftLabelEquiv_apply_one_one`: the label values `(0, 0) ↦ 0`,
  `(1, 0) ↦ 1` and `(1, 1) ↦ 2`.

## The bracketing `(C, A), B` at total rank `C + (A + B)`

Write `DR` for the outer shape
`(twoBlocks (C + A) B (Nat.add_pos_left hC A) hB).rankCast (Nat.add_assoc C A B)`.
The published `BlockShape.rankCast` keeps the length and sizes and changes only
the total rank, so `DR` has length `2` and sizes `![C + A, B]`.

- `rankCastRightRefinement : BlockRefinement DR` refines the first block of
  `DR` by `twoBlocks C A hC hA` and the second by the one-block shape of rank
  `B`. It is defined as the published `rightRefinement`, which has the same
  type up to definitional unfolding of `rankCast`.
- `rankCastRightRefinement_zero`, `rankCastRightRefinement_one`: the two inner
  shapes are `twoBlocks C A hC hA` and
  `CuspidalSupport.LeviAdmissibility.oneBlock B hB`.
- `rankCastRightRefinement_length_zero`, `rankCastRightRefinement_length_one`:
  the inner lengths are `2` and `1`.
- `rankCastRightRefinement_size_zero`, `rankCastRightRefinement_size_one`: the
  inner sizes are `![C, A]` and `fun _ => B`.
- `rankCastRightLabelEquiv` is the equivalence from the nested labels
  `(j : Fin DR.length) × Fin (rankCastRightRefinement … j).length` onto
  `Fin 3`, defined as the published `rightLabelEquiv`. The lemmas
  `rankCastRightLabelEquiv_apply_zero_zero`, `rankCastRightLabelEquiv_apply_zero_one`
  and `rankCastRightLabelEquiv_apply_one_zero` give the values `(0, 0) ↦ 0`,
  `(0, 1) ↦ 1` and `(1, 0) ↦ 2`. `rankCastRightLabelEquiv_val` gives the number
  of `⟨j, k⟩` as `2 * j + k`.
- `rankCastRightLabelEquiv_size` is the exact size law: the size of inner block
  `k` of outer block `j` equals `(threeBlocks …).size (rankCastRightLabelEquiv … ⟨j, k⟩)`.
- `rankCastRightLabelEquiv_index` is the exact coordinate identity: for every
  coordinate `x` of inner block `k` of outer block `j`,
  `DR.index j ((rankCastRightRefinement … j).index k x)` equals
  `(threeBlocks …).index (rankCastRightLabelEquiv … ⟨j, k⟩) (Fin.cast (rankCastRightLabelEquiv_size … ⟨j, k⟩) x)`.

Together with the published left data, these are exactly the arguments `S`, `e`,
`h` and the coordinate hypothesis of `OrderedProductRegrouping` for `B` the
three-block shape and `D` either `twoBlocks C (A + B) …` or `DR`, both at total
rank `C + (A + B)`.

## Proofs and provenance

All specialization, length, size and label-value lemmas hold by `rfl`.
`rankCastRightLabelEquiv_size` and `rankCastRightLabelEquiv_val` are the
published `rightLabelEquiv_size` and `rightLabelEquiv_val`, read at the
definitionally equal types. `rankCastRightLabelEquiv_index` is an instance of
the published `BlockShape.index_index_eq_of_lex` from
[`AdjacentMergeShape`](AdjacentMergeShape.md), applied to `threeBlocks`, `DR`,
`rankCastRightRefinement`, `rankCastRightLabelEquiv`, the size law and the
published lexicographic monotonicity lemma `rightLabelEquiv_lex`.

The provenance is internal: elementary finite bookkeeping for the standard
ordered decomposition of `GL_{C+A+B}` into consecutive blocks of sizes `C`, `A`,
`B`. No external theorem is used beyond the published Library declarations named
above.
