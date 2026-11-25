# Normal-base isotriviality from the normal-base local-system theorem

`Langlands.GroupScheme.multiplicativeTypeNormalIsotrivial_of_localSystem`
derives `MultiplicativeTypeNormalIsotrivialStatement.{u}` from
`Langlands.AlgebraicGeometry.EtaleLocalSystemNormalIsotrivialStatement.{u}`
in every universe. The proof applies `relativeCharacterLocalConstancy`
to the characters of the given group and passes the resulting
local-system witness and the normality hypothesis to the local-system
theorem. This supplies a finite étale surjection over an open
neighbourhood of each point, and one over the entire base when it is
irreducible.

For each cover, `Cartier.charactersBaseChangeIso` identifies the
restriction of the original character presheaf with the characters of
the pulled-back group. The proof composes the inverse of this
identification with the supplied isomorphism to the constant presheaf.
It then applies the reverse implication of `relativeCharacterConstancy`
with the supplied finitely generated coefficient group to prove
diagonalizability on the covering scheme.

This derived implication formalizes the reduction to character sheaves
in the opening paragraph of the proof of Corollary B.3.6 in Brian Conrad's
*Reductive group schemes* (2014), p. 293, registered as
`conrad-2014-reductive-group-schemes`.
[Conrad, Corollary B.3.6](https://math.stanford.edu/~conrad/papers/luminysga3.pdf#page=293)
