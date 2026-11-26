# Adjacent chambers in a Levi flat

This module derives the root geometry needed for cancellation in Arthur's Lemma 17.1 from `IsRootSet`, `IsLeviSpace`, and the chamber encoding in `GMFamilies`. It uses the supplied finite, possibly nonreduced root set in its Euclidean ambient space.

## Simple roots and projection

A finite set of vectors with a common strictly positive linear functional is generated under addition by its indecomposable members. The induction orders the vectors by the number of members of smaller functional value. Both summands in a decomposition have smaller value.

The simple roots of each chamber are linearly independent by `linearIndependent_simpleRoots` in [Root geometry for `(G, M)`-families](GMFamilyRootGeometry.md).

For a linear image of a finite positive set with independent nonzero images of the indecomposables, its nonzero image has exactly those images as its indecomposables. A decomposable lift of an image indecomposable must have one summand with zero image. Induction descends to the other summand. Conversely, a decomposition of an image of an indecomposable would split its single unit coefficient into two nonzero natural combinations, contrary to uniqueness of the coefficients. The finite positive-set induction also proves `exists_simpleRoot_combination` directly on the restricted positive roots.

## Chambers across a wall

For a simple root `v`, prescribe value zero at `v` and value one at the other simple roots. Independence and the inner-product dual give a chamber wall point with these values. At this point every positive root outside the line of `v` remains positive. A small displacement toward the opposite side preserves every sign away from that line and reverses the signs of its nonzero roots. If `-v` decomposed into two restricted positive roots in the new chamber, both summands would have zero value at the wall point. They would lie on the normal line, so negating them would give a decomposition of `v` in the original chamber. This proves `exists_adjacentAlong`.

For two adjacent chambers, quotient the Levi space by the normal line. The projected positive sets with zero removed coincide by the adjacency condition. The same indecomposable-image argument shows that the nonzero images of their simple roots coincide. The quotient map is injective on each simple root family by linear independence, including at zero, so `exists_simpleRoots_equiv_of_adjacentAlong` pairs all the simple roots. It pairs the wall root with its negative and every other root with one congruent modulo the normal line.

These are internal Euclidean consequences of the root-set axioms and the positive-root model in `GMFamilies`. They supply the chamber and wall geometry used in Arthur, *An introduction to the trace formula*, §§16–17, printed pp. 92–94, in the volume registered as `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256 `88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
