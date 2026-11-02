# The actual Isom presheaf of coherent families

`FamilyGroupoid.isomPresheaf f M N` is the presheaf of actual module
isomorphisms between the ordinary pullbacks of two published coherent-family
objects over a scheme `T`. Its domain is all of `Over T.left`, with values
in `Type (u + 1)`. There is no finiteness or reducedness restriction on
the test schemes.

The construction applies Mathlib's `Pseudofunctor.presheafHom` to the
published family-groupoid pseudofunctor after the explicit hom-universe
lift, then precomposes with `T.iteratedSliceBackward.op`. All arrows
of a family groupoid are actual module isomorphisms. The lift changes
only their universe.

`isomPointsEquiv` identifies every section with the explicit universe
lift of an isomorphism between the actual module pullbacks. Its inverse
uses the published `FamilyGroupoid.homEquiv`. The natural isomorphism
`isomPresheafLiftIso` compares the entire presheaf with the explicit
universe lift of the original family-groupoid Hom presheaf. Its proof
first checks, for an arbitrary category-valued pseudofunctor, that
lowering a lifted coherent restriction gives the original coherent
restriction. It then precomposes with the iterated-slice functor.
Thus the universe comparison includes every restriction map; the
module-isomorphism identification is stated pointwise.

This is a derived implementation of the Isom functor defined before
Lemma 99.4.1 in the original Stacks Project Section 99.4, Tag 08K7.
The retained original is `08K7.html` in registered source
`stacks-isom-functor-08k7-2026-11-02`, folder SHA-256
`a05b61ba562e7e65dd2b64446e779a6bb67af1846c0a00f4a656d64a2b2c27b5`.
Here the base map is part of the slice test object; the value retains
the actual isomorphism rather than its isomorphism class.
The retained source has no comments, and no project errata note was
present when this pair was prepared.

This pair constructs a presheaf and proves its point and universe-lift
comparisons. It proves neither scheme representability nor existence
of a coherent-stack atlas. Properness of `f` is not needed for these
definitions.
