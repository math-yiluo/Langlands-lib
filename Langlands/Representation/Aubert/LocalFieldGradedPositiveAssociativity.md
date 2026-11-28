# Associativity of three positive-rank normalized GL products

For positive ranks `a`, `b`, `c` and actual smooth representations `A`, `B`,
`C` of \(\mathrm{GL}_a(F)\), \(\mathrm{GL}_b(F)\), \(\mathrm{GL}_c(F)\) over a
nonarchimedean local field realization `T`,
`Langlands.Aubert.LocalFieldGraded.positiveAssociativityEquiv` is an
equivalence of representations from `(A × B) × C` to the pullback of
`A × (B × C)` along `GeneralLinear.reindex (finCongr (Nat.add_assoc a b c))`.
Here `X × Y` is `(binaryNormalizedProductFunctor T _ _).obj (X, Y)`. No
finite-length hypothesis is used. This is the representation-level identity
behind the associativity calculation of Zelevinsky 1980 §1.7(a), printed
p. 173, where both bracketings are identified with the induction from the
three-block Levi subgroup.

## Construction

1. `pairProductEquiv` identifies a positive-rank binary product with
   `normalizedProductInduced` on `Shahidi.twoBlocks a b`. It uses
   `binaryNormalizedProductPositiveIso`, the shape equality
   `Classification.BinaryProductBridge.binary_eq_twoBlocks` with the
   transport lemma `productShape_eq`, and the ordered factor family
   `Classification.twoBlockFactors`.
2. `regroupingEquiv` packages
   `Langlands.AllFieldBZ.Parabolic.orderedProductRegrouping`. Along an
   ordered refinement of a coarse block shape `D` into a fine shape `B`, it
   identifies the normalized product over `B` with the normalized product
   over `D` of the blockwise products. It uses
   `Langlands.AllFieldBZ.FiniteTensor.glRefinementEquiv` and the three
   theorems `refinementCoordinatesNormalization`,
   `normalizedRefinementInductionTransitivity` and `refinedInductionTensor`
   of `Langlands.AllFieldBZ.Parabolic`. `regroupingEquiv` then composes this
   isomorphism with blockwise equivalences through
   `normalizedProductInducedEquiv`.
3. `regroupRightPair` applies it to `threeBlocks a b c` with the refinement
   `leftRefinement` of the two-block shape `(a, b + c)`. The first block is a
   one-block product, which `singleBlockTransportedProductEquiv` evaluates
   to `A`. The second is the two-block product of `B` and `C`, identified by
   `pairFamilyEquiv`. `regroupLeftPair` applies it to `threeBlocksRight a b c`
   with `rightRefinement` of the shape `(a + b, c)`, in the same way. The
   index and size equations come from `leftLabelEquiv_size`,
   `leftLabelEquiv_index`, `rightLabelEquiv_size` and
   `rightLabelEquiv_index` of `Langlands.Representation.Parabolic.ThreeBlockRefinementGeometry`.
4. `inducedRankCast` identifies the pullback of the three-block product of
   rank `a + (b + c)` along the reindexing with the product on
   `(threeBlocks a b c).rankCast`, which is `threeBlocksRight a b c` at rank
   `(a + b) + c` by definition (`threeBlocksRight_eq_rankCast` is `rfl`).
5. `positiveAssociativityEquiv` composes: the outer and inner binary
   products of each bracketing are rewritten by `pairProductEquiv`, then the
   inverse of `regroupLeftPair`, the inverse of `inducedRankCast`, and the
   pullback along the reindexing of `regroupRightPair` followed by the
   inverse of the rewritten right bracketing. The compositions use the
   explicit equivalence operations `equivTrans`, `equivSymm` and
   `equivPrecomp`.

## Provenance

The module is an internal consequence of results in the Library: the
regrouping theorem `orderedProductRegrouping`, which compares normalized
products along an ordered refinement of block shapes, and the block-shape
bookkeeping above. Zelevinsky 1980 §1.7(a), printed p. 173, derives the
associativity identity from transitivity of induction (§1.1(c)) and the
tensor-coordinate form of induction (§1.5); the regrouping theorem plays
both roles here. The two declarations of the modules under
`Langlands/Representation/Classification` that this module names,
`binary_eq_twoBlocks` and `twoBlockFactors`, are an equality of two
descriptions of the same two-block shape and the ordered pair family on
`Fin 2`.
