# Positive simple-root conjugacy from actual root-span reflections

This internal derived module concerns the actual scheme relative Weyl quotient,
its action on the character lattice, and the literal simple relative roots of a
generic cocharacter. `PositiveSimpleReflectionLaw` states that, when the image of
a simple root is positive, conjugacy of its labelled reflection to another
simple reflection is equivalent to equality of the image character with the
second simple root.

The hypotheses are the given actual relative-root-system witness, a split
torus, a generic cocharacter, and a supplied Coxeter system whose simple
generators are actual root-span relative reflections. No full-character
integral-coroot realization is assumed. Nonreduced systems are allowed.

The forward proof identifies the witness root indices and its functional base
with the actual root characters and simple labels. The faithful linear image
identifies its Weyl group with the actual quotient. Uniqueness of an actual
relative reflection identifies each supplied generator with its witness root
reflection. Genericity makes the witness functional regular, and positivity and
conjugacy transport to the root pairing. `RootPairingSigns.root_eq_of_conj_simple`
then gives equality of root vectors, including in a nonreduced system. The
split torus's injective rationalization and the compatibility of the actions
recover literal equality of characters.

For the reverse implication, conjugating an actual reflection gives the
reflection in the image root. Equality of that character with the target label
and uniqueness of actual relative reflections give the required group equality.
The final corollary uses `isRelativeReflection_simple_of_rootLength` to obtain the
same law for any supplied system satisfying the root-sign length law.

The provenance is the internal combination of `RelativeRootCoxeterConstruction`,
`RootPairingSigns`, `RelativeReflectionProperties`, and
`IsRelativeReflection.conj`. This module does not claim the rational-point
representation expansion or the final Aubert compatibility equation.
