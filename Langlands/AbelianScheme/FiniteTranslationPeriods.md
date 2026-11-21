# The finite subgroup of translation periods of a finite map

`exists_finiteTranslationPeriods` represents the translation periods of a
finite morphism from a reduced abelian variety over a field to a separated
scheme over that field. A dense family of rational points tests a period by
comparing the translated and constant images of each member of the family.
The comparison takes place on the whole test scheme, including its
nilpotents. The representing group is a finite closed subgroup of the
abelian variety. Its points preserve the morphism on every test scheme.

The simultaneous closed equalizer represents the test equations. It is
finite over the field because a single equation embeds it as a closed
subscheme of the fibre of a translated finite map. Pull the complete family
of equations to the product of the equalizer with the abelian variety. On
each rational fibre, the two resulting morphisms agree. The density lemma
extends the equality to the product, yielding invariance under the universal
point of the equalizer. This equality identifies the represented functor
with the subgroup functor of translations that preserve the map after any
further restriction. The Library's representability transfer constructs
its group law and the subgroup inclusion.

This auxiliary construction implements the finite period subgroup for the
complete linear system used in the Lefschetz argument. The original use of
translation subgroups to rule out failures of separation is in Mumford,
*Abelian Varieties*, §17, printed pp. 164–165 (PDF p. 87 of
`mumford-abelian-varieties-full-scan`).
