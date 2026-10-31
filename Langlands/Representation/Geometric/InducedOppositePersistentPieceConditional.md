# A selected whole opposite geometric piece under change of inducing object

Authors: Worker 99 and Worker 954.

This module extends Worker 954's `cuspidalPiece_of_geometricLemma` construction.
It takes the geometric lemma for `(B, C.reverse)` as an explicit input.
`InducedCuspidalExponentPersistenceProof` supplies the published closed
geometric lemma when using this construction in the persistence proof.

`persistentCuspidalPiece_of_geometricLemma` selects one finite geometric-lemma
index responsible for the irreducible cuspidal constituent of the opposite
Jacquet module of induction. Proper target refinements are excluded by the
published `GeometricExcessBranch.not_isSubquotient_properInduced` theorem,
as in the integrated cuspidal-piece construction. The source refinement `S`, permutation `w` and conjugacy proof
`hw` then identify this same whole-target piece for every smooth inducing
object `V` with carrier in the same universe. Every such piece is an actual
subquotient of `oppositeJacquet (induced V)`, by the *same* gluing index.

The second conclusion is proved by `IsGluedFrom.isSubquotient_piece`, followed
by `wholeLeviGeometricPieceEquiv`, pullback through `leviReverseEquiv`,
`transportReverseEquiv`, and `oppositeJacquetReverseEquiv`. It does not compare
labels by equivalence and does not assert that every cuspidal constituent
occurs at every inducing object. Later real-character compatibility must
supply the particular constituent at the untwisted object.

The construction is an internal derived consequence of BZ77 Theorem 2.12 and
2.4(d), inherited through the imported Library results and Worker 954's
`InducedOppositeCuspidalPieceConditional` module. Its additional step retains
the selected gluing index and applies its inclusion to another inducing object.
