# Simultaneous cuspidal presentations inside a standard Levi

Worker 1437 derives a same-datum cuspidal presentation for an irreducible
smooth representation of the literal standard Levi `M_J(F)`. The universes
`uF` and `uV` are independent; every representation carrier remains in
`max uF uV`. No support comparison, uniqueness, decomposition, or
representation-theoretic premise is assumed.

The noncomputable constructor `bernsteinLeviCuspidalJacquetPresentation`
chooses the subset and datum as a pair, with the roots equality, Jacquet
quotient and induction embedding retained in the subtype property. It uses
classical choice on the following existence theorem. The Prop-valued
`bernsteinLeviCuspidalPresentationProperty` names precisely the roots equality
and the two witnesses; it adds no representation-theoretic premise.

The theorem
`exists_bernsteinLeviCuspidalDatum_jacquet_quotient_induction_embedding`
produces a subset `I` of `J`, a genuine `BernsteinCuspidalDatum` `b` with
roots `leviIndex J I`, a quotient of the actual normalized inner Jacquet
module onto the literal representation of `b`, and an embedding of the
original irreducible into normalized induction inside `M_J` from that same
representation.

The proof retains the quotient witness in the published construction
`exists_cuspidal_embedding_in_levi`. Minimal nonzero inner Jacquet restriction
is cuspidal. Compactness of the literal inside-Levi parabolic quotient
follows from the published dynamic quotient-compactness theorem by projecting
ambient compact representatives. Finite generation of the Jacquet module
then supplies an irreducible quotient. Normalized first adjointness gives
the induction embedding, and surjective transport preserves cuspidality.
The canonical homeomorphism between rational points of the represented Levi
scheme and the literal subgroup turns this quotient into genuine Bernstein
data. The resulting round-trip isomorphism transports both witnesses. Generic
helpers compose a quotient with the inverse isomorphism and an embedding
with the inverse of the induced isomorphism; specializing them avoids
unfolding the concrete normalized induction object during elaboration.

This is derived internal content following
`RationalLeviCuspidalEmbedding`, `CuspidalQuotientEmbedding`,
`RationalLeviQuotientCompactness`, and `BernsteinCuspidalSupportExistence`.
Its source context is Renard, *Représentations des groupes réductifs
p-adiques*, French version of 9 July 2026, VI.7.1 and the deduction in
VI.7.3 (printed p.185 / PDF p.191), registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This theorem alone does not establish inertia compatibility with an
ambient block.
