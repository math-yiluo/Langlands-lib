# Radical action and assembly for the actual Levi presheaf

This internal helper connects the actual relative Levi presheaf to the
generic presheaf torsor constructions. The geometric source is Conrad,
*Reductive group schemes* (2014), Corollary 5.4.6, p.178, source identifier
`conrad-2014-reductive-group-schemes`.

For a relative parabolic in a reductive group and a supplied radical,
`moduliAction` records actual conjugation on every test. Its naturality is
the published compatibility of restriction and conjugation. Arbitrary
parabolic base change allows the published unique conjugacy theorem to
apply on every test base. The canonical point equivalence identifies
radical points over that base with test-valued points of the original
radical. No global Levi point is required.

A presheaf representation gives exactly `ModuliRepresentation`, including
the prescribed equality of all-test subgroup images under literal
restriction. The generic represented action is equivariant in the
required orientation and has invertible `leftSMul`. A smooth affine
surjective model therefore supplies the target's flat, surjective and
quasi-compact morphism and all its action and representation conclusions.
Existence of that model is a separate obligation.

Finally the canonical direct/iterated pullback comparison gives a natural
isomorphism from the changed-base Levi presheaf to restriction of the
original presheaf. Its proof chooses a presentation only to verify that
both restriction routes give the same actual subgroup functor; naturality
of the actual family homomorphisms proves the equality.
