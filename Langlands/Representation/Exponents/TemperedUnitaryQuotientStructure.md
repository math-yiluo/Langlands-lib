# Admissibility and full-center characters of unitary Jacquet quotients

This internal supporting derivation supplies admissibility and a scalar
full-center character for the selected irreducible quotient in Renard,
*Représentations des groupes réductifs p-adiques*, 9 July 2026, VII.2.6,
first proof paragraph, printed p.231 / PDF p.237. The source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These are prerequisites for applying the separately stated VII.2.4
square-integrability criterion to that quotient; they do not apply the criterion.

The ambient hypotheses are a connected reductive group over a Hausdorff
nonarchimedean local field, with the canonical rational-point topology and the
given locally compact and nonarchimedean-group instances. The field universe
`u` and representation carrier universe `v` are independent. Every actual
parabolic, rational Levi, matching geometric radical, multiplication isomorphism,
and split component is retained. The input
`UnitaryJacquetIrreducibleQuotientData` stores a genuine irreducible smooth
quotient on the Levi's own rational points and its surjective quotient map.

`UnitaryJacquetIrreducibleQuotientData.isAdmissible` obtains admissibility of
the full normalized Jacquet module from source temperedness and its compatible
presentation coverage. The published topological group equivalence transports
this admissibility to the Levi's own point group. The quotient map extends to
the full Jacquet module using the complementary unitary-part retraction, and
that extension is surjective. Compact-open averaging therefore makes every
compact-open fixed-vector space of the quotient a quotient of a finite source
fixed-vector space. Containment of a compact open subgroup in every open
subgroup proves the all-open-subgroups admissibility convention.

`existsUnique_centralCharacter` applies the published admissible Schur theorem
to this admissibility and the stored irreducibility. It gives a unique locally
constant character of the full center of the actual Levi rational-point group,
acting by scalars. It does not assert that the character is unitary or identify
it merely with a character on the split component.

`UnitaryJacquetIrreducibleQuotientData.centralCharacter` chooses this scalar
character as an actual multiplicative map on the full center.
`centralCharacter_spec` proves its local constancy and scalar action; the
existence-and-uniqueness theorem above makes the selected map independent of
any alternative character with those properties.

The construction and its properties are derived from the published actual Jacquet, group transport,
compact averaging, and admissible Schur constructions. They add no
Jacquet-admissibility, presentation-existence, central-character, finite-length,
or quotient-compactness premise. They do not establish temperedness of the
unitary Jacquet module or the quotient, nested transitivity, square-integrability,
or any of the three final VII.2.6 propositions.
