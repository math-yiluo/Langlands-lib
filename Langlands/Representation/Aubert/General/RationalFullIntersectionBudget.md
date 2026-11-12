# Full-intersection pairs and actual source cosets

This internal derived helper supplies the numerical Weyl comparison used in the
length bound of Renard, *Représentations des groupes réductifs p-adiques* (9 July
2026), V.4.3–V.4.4, printed p.119 / PDF p.125, and VI.5.4, printed pp.173–174 /
PDF pp.179–180. It does not assert the representation-theoretic length bound.

Fix actual rational points of a connected reductive group, a maximal split torus,
a generic cocharacter, and the actual standard Levi family. The hypotheses
retain the standard-cocharacter theorem, the point normalizer and centralizer
comparisons, a finite actual Coxeter system with its root-sign length and
positive-simple-reflection comparisons, and the actual Levi Weyl identification.

`standardLeviTransportingWeyl i ν I` is the literal set of Weyl elements with a
normalizer lift conjugating the source Levi `M_I` onto some standard Levi.
`standardLeviTransporterSourceCosets` is its image in the quotient by the image
of the source Levi Weyl group. Thus it counts left cosets `w W_I` with the source
on the right, exactly as in the source-coset expression for `l(M)` in V.4.4 and
in the published Lean numerical-bounds statement.

`fullIntersectionPairTransporterEmbedding` retains the target subset and Weyl
element of every pair in `fullIntersectionPairs cs I`. Such a pair has
equal source and target cardinalities, is minimal in the target/source double
coset, and has full source intersection. The published root-sign comparison
therefore gives equality of the source and target simple-root images. Choosing
a normalizer lift of that same Weyl element yields root association, and the
actual standard-Levi conjugation theorem supplies literal forward conjugation.
This constructs a selected actual minimal transporter, with selection always
true. The embedding is injective because it preserves the pair.

`card_fullIntersectionPairs_le_sourceCosets` composes this injection with the
actual minimal-transporter source-coset inequality. Centralizer containment
follows from its actual point comparison and containment in every standard
Levi; injectivity of the Levi family follows from the actual Levi Weyl
identification. Rearranging existential witnesses identifies the resulting
coset image with `standardLeviTransporterSourceCosets`. All cardinalities are
finite under the explicit finite simple-root and finite Weyl assumptions.

The module supplies only this combinatorial comparison. Actual geometric
filtration budgets and irreducible Jacquet detection remain separate inputs
to the representation-length argument.
