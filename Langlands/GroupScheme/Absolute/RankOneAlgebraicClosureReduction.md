# Algebraic-closure reduction for opposite Lie-weight exclusion

This internal reduction separates the arbitrary-field part of the solvable
obstruction from its geometric Borel case.

`RankOneAlgClosedBorelExclusionStatement` asks for the following result at
universe `u`: over an algebraically closed field, a Borel subgroup of a connected
reductive group containing the specified split maximal torus cannot have nonzero
actual Lie-image witnesses of both weights `α` and `-α`, for any root `α`.
The torus factors through the specified Borel by an actual group-scheme
homomorphism. The statement uses `Lie.MeetsWeightSpace`, so each witness includes
a nonzero ambient weight vector and a preimage under the actual tangent map.
The definition does not assert that this Borel case is proved.

`IsSolvableGroupScheme.baseChange_toAlgebraicClosure` proves that a solvable group
scheme remains solvable over the chosen algebraic closure. By definition, its
original solvability hypothesis is solvability of that base-changed group's
rational points. Over an algebraically closed field,
`isSolvableGroupScheme_iff_isSolvable_points` converts precisely this hypothesis
to group-scheme solvability. No smoothness or affineness is needed for this
lemma, and no assertion about arbitrary field-extension solvability is used.

`rankOneSolvableObstruction_of_algClosedBorel` proves the exact public
`RankOneSolvableObstructionStatement` conditionally on
`MaximalTorusBaseChangeForwardStatement` and
`RankOneAlgClosedBorelExclusionStatement`. Both are explicit premises and remain
proof obligations.

For an arbitrary original field `k`, the proof pulls back the ambient group,
the specified torus, the original solvable subgroup `H`, and its torus
factorization along `Spec k̄ → Spec k`. Published
`IsConnectedReductive.baseChange_toAlgebraicClosure` supplies connected
reductivity of the ambient pullback. Splitness of the torus and closedness of
the subgroup persist by published base-change lemmas. Maximality of the torus
uses the explicit forward-preservation premise. Smoothness of `H` persists by
the pullback instance; its affineness follows from its closed embedding into
the affine ambient group. Published
`connectedSpace_baseChange_of_smooth_affine` then supplies connectedness.
The new solvability lemma supplies the remaining solvability hypothesis.
Functoriality preserves the given torus factorization exactly.

The proof applies the published Borel-containment reduction
`not_meets_oppositeWeightSpaces_of_borel` to this actual pullback of `H`.
That reduction chooses a Borel containing it and composes the original torus
factorization with its inclusion. The Borel-exclusion premise therefore applies
without any preservation theorem for an originally chosen Borel subgroup.

Finally, published `mem_roots_baseChange_iff` carries the original root to its
pulled-back character. Each original Lie-image witness is transported by
`weightSpace_lieImage_baseChange`, which preserves its nonzeroness, weight and
actual tangent preimage. Additivity of character pullback identifies the
pulled-back negative weight with the negative of the pulled-back character.
The resulting pair contradicts the exclusion just obtained over `k̄`.

All fields, characteristics and universe `u` are retained, including imperfect
fields. This pair is an internal assembly of the cited Library declarations
and the existing definition of solvability; it introduces no new external
structural assertion. It does not prove either retained premise or provide an
unconditional proof of the rank-one solvable obstruction.
