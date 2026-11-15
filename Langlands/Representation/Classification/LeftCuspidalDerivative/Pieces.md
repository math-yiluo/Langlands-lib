# First-block constituents of the geometric pieces of a binary product

Lean module: `Langlands.Representation.Classification.LeftCuspidalDerivative.Pieces`.

An internal module of the proof of
`Langlands.Classification.LeftCuspidalDerivative.LeftCuspidalDerivativeLemma`. It proves the
internal statement `BinaryGeometricPieces.BinaryGeometricPieceConstituents` (module
`BinaryGeometricPieceConstituentsStatement`): the theorem `binaryGeometricPieceConstituents`.
That statement describes the irreducible constituents of the first block of a geometric piece
of `r_(a,b)(Y₁ × Y₂)`. It is the two-block case of the analysis of the geometric lemma
(Bernstein–Zelevinsky 1977, §2.12 and Theorem 5.2). The proof is
assembled from the earlier internal modules `PieceStructure` (structure of one block of a
piece), `PieceCombinatorics` (where inner blocks come from), `PieceTools` (slot restrictions)
and from Library results on single-block shapes and binary products. The module claims
nothing beyond the Lean statements below.

Notation: `IsFirstBlockConstituent F T Y ρ` and `IsMixedConstituent F T Y₁ Y₂ ρ` are the
definitions of the statement module. `ρ` is a first-block constituent of `Y` if either the
ranks agree and `ρ` is a subquotient of the rank cast of `Y`, or `ρ` is a subquotient of the
restriction to the first block `GL_a` of the normalized Jacquet module of `Y` along a
two-block shape `(a, k)`. `ρ` is a mixed constituent if it is a subquotient of the rank cast
of a normalized binary product `ρ₁ × ρ₂` of irreducible first-block constituents `ρ₁` of `Y₁`
and `ρ₂` of `Y₂`.

## Helpers

Rank casts (`castRank h A := h ▸ A`):

* `castRank_trans`, `castRank_self`, `castRank_family_eq`: rank casts compose, the cast
  along `r = r` is the identity, and casts of one family at equal indices agree.
* `flattenedBlockFactor_eq` (by `rfl`): the factor
  `Parabolic.flattenedBlockFactor T B S X i j` is the rank cast of
  `X (B.flattenBlockEquiv S ⟨i, j⟩)`.
* `flattenedBlockTensor_eq`, `flattenedBlockTensor_representation` (by `rfl`): the regrouped
  tensor `Parabolic.flattenedBlockTensor T B S X i` is the external tensor product of the
  factors `flattenedBlockFactor T B S X i j`.
* `flattenedBlockFactor_transport`: for `hw : ConjugatesLevi (B.flatten S) (C.flatten R) w`,
  the factor in an inner block `q` of `R` of the relabelled family
  `k ↦ castRank _ (X ((blockEquiv hw).symm k))` is the rank cast of the factor of `X` in the
  source inner block `sourceBlock hw q` (`PieceCombinatorics`). Proof: unfold both factors
  into rank casts, compose, and use `flattenBlockEquiv_sourceBlock`.

Block shapes:

* `exists_eq_ofPair`: a block shape with two blocks equals `BlockShape.ofPair a k ha hk h`
  for its two sizes (`TotalConjugatingCount.shape_ext`).
* `size_add_size_of_length_eq_two`: the two sizes of a two-block shape add up to the rank.
* `length_pos_of_pos`: a block shape of positive rank has a block.

## First-block constituents

* `isFirstBlockConstituent_of_isSubquotient`: a subquotient (in the sense of
  `WeylBranchPieces.IsSubquotient`) of a first-block constituent is a first-block
  constituent (transitivity of subquotients).
* `isFirstBlockConstituent_castRank`: first-block constituents are stable under rank casts
  (`subst`).
* `isFirstBlockConstituent_of_isSubquotient_jacquet`. Let `D` be a block shape of `GL_m`
  with at most two blocks, and `Z` a family of irreducible representations of its blocks
  whose external tensor product is a subquotient of the normalized Jacquet module of `Y`
  along `D`. Then the factor `Z j` in the first block (`j = 0`) is a first-block
  constituent of `Y`.
  Proof: restricting to the block `GL_{D.size j}` (`MonoidHom.mulSingle`), `Z j` is a
  subquotient of the restriction of the Jacquet module. This uses
  `isSubquotient_external_comp_mulSingle` (the other factors are nonzero, as irreducible
  representations are nontrivial). If `D` has one block, the Jacquet module is the rank cast
  of `Y` (`singleBlockNormalizedJacquetTensorEquiv`). Then
  `isSubquotient_factor_of_external_comp_mulSingle` gives the first alternative. If `D` has
  two blocks, `D = ofPair a' k'` and this is the second alternative.

## Induction along one block of `C`

* `isSubquotient_castRank_of_singleBlock`: if `D` has one block, a subquotient of the
  normalized induction along `D` of `externalSmoothObject Z` is a subquotient of the rank
  cast of the unique factor (`singleBlockNormalizedProductEquiv`, `castRankEquiv`).
* `isSubquotient_binaryProduct_of_twoBlock`: if `D` has two blocks, a subquotient `ρ` of
  the normalized induction along `D` of `externalSmoothObject Z` is a subquotient of the rank
  cast of the normalized binary product
  `(T.binaryNormalizedProductFunctor _ _).obj (Z 0, Z 1)`. Proof: write `D = ofPair a' k'`
  and use the isomorphism `SegmentSocleDerivativesProof.nonempty_ofPairProductIso` between
  the binary product and the induction along `ofPair`. The family `twoBlockFactors` of the
  two factors equals `Z`.

## Main results

* `isFirstBlockConstituent_flattenedBlockFactor`. Data: two-block shapes as below with
  `C.length = 2`, a minimal representative `w`, `hS`, an abstract conjugation
  `hw : ConjugatesLevi (B.flatten S) (C.flatten R) w`, and a family `X` of irreducible
  representations on `B.flatten S` such that each regrouped tensor
  `flattenedBlockTensor T B S X i` is a subquotient of the normalized Jacquet module of `Y i`
  along `S i`. Conclusion: for the first block `j₀` of `C` (`j₀ = 0`) and every inner block
  `l` of `R j₀`, the factor in `⟨j₀, l⟩` of the relabelled family is a first-block
  constituent of `Y (sourceBlock hw ⟨j₀, l⟩).1`.
  Proof: the source inner block is the first inner block of its block
  (`sourceBlock_snd_eq_zero`), and that block of `B` has at most `C.length = 2` inner blocks
  (`refinement_length_le`). Then apply `isFirstBlockConstituent_of_isSubquotient_jacquet`,
  the rank-cast lemma and `flattenedBlockFactor_transport`.

* `pieceConstituents_of_factors` (the case analysis). For two-block shapes `B`, `C` of `n`,
  a minimal representative `w`, `hS`, an abstract `hw`, the first block `j₀` of `C`, and `X`
  as above with `ρ` a subquotient of the normalized induction along `R j₀` of the regrouped
  relabelled tensor in the block `j₀`. Conclusion: `w = 1` and `ρ` is a first-block
  constituent of `Y 0`; or `ρ` is a first-block constituent of `Y 1`; or `ρ` is a mixed
  constituent of `Y 0` and `Y 1`.
  Proof: `R j₀` has one or two inner blocks (`length_le_of_sourceBlock`, `length_pos_of_pos`).
  * One inner block: `ρ` is a subquotient of the rank cast of its factor
    (`isSubquotient_castRank_of_singleBlock`), hence a first-block constituent of the source
    block of `B`. If this source block is block `0`, then `w = 1`
    (`eq_one_of_sourceBlock`). Otherwise it is block `1`.
  * Two inner blocks: they come from blocks `0` and `1` of `B`, in this order
    (`sourceBlock_fst_val_of_length_two`). Their factors are irreducible first-block
    constituents of `Y 0` and `Y 1`, and `isSubquotient_binaryProduct_of_twoBlock` gives
    the mixed alternative.

* `pieceConstituents_of_twoBlocks`: the same conclusion when `ρ` (irreducible) is a
  subquotient of the restriction to the block `j₀` of the geometric piece
  `(geometricPieceFunctor T B C w S R hS hR).obj (externalSmoothObject Y)`, for a family `Y`
  of finite-length representations. Proof: `exists_factors_of_isSubquotient_geometricPiece`
  (`PieceStructure`) supplies `X`. Then apply `pieceConstituents_of_factors` with
  `hw := conjugatesLevi_flattened_intersections ... hS hR`.

* `binaryGeometricPieceConstituents : BinaryGeometricPieceConstituents.{uF, uV}`. Proof:
  apply `pieceConstituents_of_twoBlocks` with `B = ofPair m₁ m₂`, `C = ofPair a b`, the
  family `twoBlockFactors h₁ h₂ Y₁ Y₂` (finite length blockwise), and `j₀ = 0`.

## Implementation notes

The universe level of the coefficient spaces appears in several lemmas only as `max uF uV`.
The universe arguments are then passed explicitly (`.{uF, uV}`), since leaving
`max uF ?v` to unification led to `whnf` timeouts. The hypothesis of the statement is passed
as `(by with_reducible exact hsub)`, for the reason explained in `Product.md`.
