# Ordered refinement data for the two bracketings of three blocks

Author: Worker 832.

This internal module supplies the finite combinatorial data needed to apply
the ordered regrouping proposition `Parabolic.OrderedProductRegrouping` to
three consecutive blocks of positive ranks `C`, `A` and `B`, in each of the
two possible bracketings. It is pure block-shape bookkeeping. It constructs
no representation, and it does not assume or prove a regrouping theorem or
three-block associativity.

## Shapes

All declarations take the explicit natural numbers `C A B` and the positivity
hypotheses `hC : 0 < C`, `hA : 0 < A`, `hB : 0 < B`.

- `CuspidalSupport.LeviAdmissibility.oneBlock m hm` is the block shape of total rank `m` with exactly one
  block, of size `m`, imported from
  [`OneBlockShape`](../../Group/GL/OneBlockShape.md).
- `threeBlocks C A B hC hA hB` is the ordered shape with three blocks of sizes
  `![C, A, B]` and total rank `C + (A + B)`.
- `threeBlocksRight C A B hC hA hB` is the same ordered shape `![C, A, B]`
  with total rank `C + A + B`, that is `(C + A) + B`.
- `threeBlocksRight_eq_rankCast` records that `threeBlocksRight` is
  definitionally the published `BlockShape.rankCast` of `threeBlocks` along
  `(Nat.add_assoc C A B).symm`.

## The bracketing `C, (A, B)`

The outer shape is the published `twoBlocks C (A + B)`.

- `leftRefinement` is the `BlockRefinement` of that outer shape whose first
  block is refined by `CuspidalSupport.LeviAdmissibility.oneBlock C` and whose second block is refined by
  `twoBlocks A B`.
- `leftLabel` numbers the nested labels consecutively: the label of the
  first outer block goes to `0`, and the inner label `k` of the second outer
  block goes to `k.succ`. `leftLabelInv` is the inverse numbering, and
  `leftLabelEquiv` packages both as an equivalence from the nested labels
  `(j : Fin 2) × Fin (leftRefinement … j).length` onto `Fin 3`.
- `leftLabelEquiv_size` is the exact size law: the size of inner block `k` of
  outer block `j` equals the size in `threeBlocks` of its number.
- `leftLabelEquiv_val` computes the number of `⟨j, k⟩` as `j + k`, and
  `leftLabelEquiv_lex` shows that the numbering is strictly increasing for the
  lexicographic order of outer and inner labels.
- `leftLabelEquiv_index` is the exact ambient consecutive-coordinate
  identity: for every coordinate `x` of inner block `k` of outer block `j`,
  `(twoBlocks C (A + B)).index j ((leftRefinement … j).index k x)` equals
  `(threeBlocks …).index (leftLabelEquiv … ⟨j, k⟩) (Fin.cast (leftLabelEquiv_size … ⟨j, k⟩) x)`.

## The bracketing `(C, A), B`

The outer shape is the published `twoBlocks (C + A) B`.

- `rightRefinement` refines its first block by `twoBlocks C A` and its second
  block by `CuspidalSupport.LeviAdmissibility.oneBlock B`.
- `rightLabel` sends the inner label `k` of the first outer block to
  `k.castSucc` and the label of the second outer block to `2`;
  `rightLabelInv` and `rightLabelEquiv` are the inverse and the packaged
  equivalence onto `Fin 3`.
- `rightLabelEquiv_size` is the size law against `threeBlocksRight`,
  `rightLabelEquiv_val` computes the number of `⟨j, k⟩` as `2 * j + k`, and
  `rightLabelEquiv_lex` is lexicographic strict monotonicity.
- `rightLabelEquiv_index` is the exact consecutive-coordinate identity for
  `twoBlocks (C + A) B`, `rightRefinement` and `threeBlocksRight`, of the same
  form as in the left case.

The equalities `leftLabelEquiv_size`, `rightLabelEquiv_size` and the label
computations hold definitionally, case by case, so transported factor
families `(h ⟨j, k⟩).symm ▸ σ (e ⟨j, k⟩)` reduce on concrete labels.

## Proofs and provenance

The equivalence laws, size laws, value computations and lexicographic
monotonicity are proved by finite case analysis over the at most three nested
labels. The two coordinate identities are instances of the published
`BlockShape.index_index_eq_of_lex`, applied with the respective size law and
monotonicity lemma.

The provenance is internal: elementary finite bookkeeping for the standard
ordered block decomposition of `GL_{C+A+B}` into blocks of sizes `C`, `A`,
`B`, with no external theorem asserted beyond the published Library lemma
named above.
