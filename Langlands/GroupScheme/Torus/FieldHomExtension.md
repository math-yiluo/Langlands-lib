# Extending field-fibre homomorphisms between split tori

For a scheme `S`, a field `k`, a specified morphism `b : Spec k ⟶ S`, and two
commutative group schemes `T` and `T'` over `S` which are split tori,
`IsSplitTorus.hom_fieldBaseChange_surjective` states that base change along `b`
is surjective on their actual group-scheme homomorphisms. The scheme and field
have arbitrary common universe `u`. No connectedness, reducedness or affineness
hypothesis is imposed on `S`. This is an existence assertion and does not claim
uniqueness over an arbitrary base. `IsSplitTorus.fieldHomExtension` chooses
such an extension, and `IsSplitTorus.fieldHomExtension_baseChange` is the exact
base-change equality recovering the specified field map.

This is a derived internal result. Choose finite standard split-torus
presentations of source and target, and use the canonical base-change
identifications to express the specified field homomorphism in those
coordinates. Its pullback on integral character coordinates is realized over
`S` by `splitTorus.exponentHom`. The published
`splitTorus.exponentHom_characterMap` recovers the given field homomorphism,
and `splitTorus.exponentHom_baseChange` gives compatibility with `b`. Conjugating
by the chosen presentations gives the required actual homomorphism. This is
the homomorphism analogue of the existing split-torus automorphism extension
argument in `Torus/HenselianNormalizerLifting`; no new literature assertion
is introduced.
