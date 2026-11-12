# Rational points over an extension of henselian valued fields: proof

Author: Worker 114.

`Langlands.AlgebraicGeometry.AlgebraicSpace.henselianExtensionPointEmbedding`
proves the unchanged proposition
`HenselianExtensionPointEmbeddingStatement.{u}`. The target's source attribution
and conventions are documented in
[its statement explanation](HenselianExtensionPointEmbeddingStatement.md).
The proof here is an internal composition of published Library results.

The Lean term applies
`ExtensionClosedReduction.henselianExtensionPointEmbedding_of_complete`
to `CompleteExtensionClosedRange.completeExtensionPointClosedRange`.
The latter proves `CompleteExtensionPointClosedRangeStatement.{u}` for arbitrary
extensions of complete nontrivially normed fields and separated spaces.
The former consumes exactly that proposition and produces the full target.

The reduction already proves embedding by localization through separated open
subspaces. For conditional closedness, it completes both fields and uses the
complete-field theorem to obtain a closed rational locus over the completed
base. Pulling this locus back along coefficient extension to the completed
extension gives precisely the original rational locus, by the published
completion-intersection lemma when the base field is closed in the extension.
Separated-open localization then gives closed range for the covered space;
together with embedding, this is the required closed embedding.
These steps are implemented in
[the reduction](HenselianExtensionClosedReduction.md); the complete-field
proof is explained in
[the complete-field module](CompleteExtensionPointClosedRangeProof.md).

Thus the theorem keeps arbitrary henselian nontrivially normed field extensions,
including infinite and transcendental extensions, and every quasi-separated
algebraic space locally of finite type covered by separated open subspaces.
Its map and both topologies are exactly those in the target statement.
Closed embedding retains the statement's condition that the image of the base
field is closed in the extension. Completeness is used only inside the
imported reduction and complete-field theorem.
