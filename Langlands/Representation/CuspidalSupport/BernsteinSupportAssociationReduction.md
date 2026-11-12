# Actual Bernstein association from represented VI.5.4

This supporting reduction connects the original actual Bernstein support
relation to the published represented-parabolic VI.5.4 target. The latter
remains an explicit hypothesis. It does not assert unconditional support
uniqueness or a Bernstein decomposition.

The represented standard point images coincide with the literal standard
parabolic, Levi and unipotent subgroups. Both canonical maps from the actual
rational Levi send a point to its original algebraic inclusion into the
ambient group. The published embedded-Levi induction comparison therefore
gives an isomorphism from represented induction to `bernsteinInduction`.

Each Bernstein datum satisfies represented supercuspidality by the
unconditional adapter `BernsteinCuspidalDatum.isSupercuspidal`. Given a common
irreducible actual subquotient of two Bernstein inductions, the comparison
isomorphisms make it a common constituent of the represented inductions.
Implication (iv) to (i) of the supplied VI.5.4 theorem supplies an ambient
rational point, an algebraic Levi isomorphism, compatibility of the original
embeddings and an equivariant linear equivalence. These are exactly an
actual `RationalLeviConjugacy` and an isomorphism of one original
representation with the rational algebraic pullback of the other.
The implementation separates the implication extraction, the pointwise
intertwiner-to-isomorphism construction, the represented witness for two
independent standard root sets, and its packaging into actual association.
The main theorem applies these helpers to the original datum representations.
`bernsteinCuspidalSupportAssociationWitnessOfRepresented` chooses an actual
`RationalLeviConjugacy` and its equivariant pullback isomorphism from this
proved existential statement; its output is a dependent pair in `Type`.
The published association-to-inertia lemma then proves uniqueness of the
original quotient-valued support relation.

The source is Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, VI.5.4 Theorem, printed pp.173–174 /
PDF pp.179–180, and VI.7.1–VI.7.2, printed pp.181–184 / PDF pp.187–190.
Source ID `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This is an internal adapter between the Library's actual interfaces; the
source VI.5.4 proof remains a separate prerequisite.
