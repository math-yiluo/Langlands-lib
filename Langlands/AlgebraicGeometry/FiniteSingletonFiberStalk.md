# Finite stalks and closed immersion near a singleton fiber

The theorem
`Langlands.AlgebraicGeometry.finiteSingletonFiber_localClosedImmersion`
proves the complete unchanged published proposition
`Langlands.AlgebraicGeometry.FiniteSingletonFiberLocalClosedImmersionStatement`
by importing its same-name Library module. The imported statement and all
its dependencies are preserved.

The schemes have any common universe. The map is finite and its entire
underlying topological fiber at the selected image is a singleton. The result
states that its actual stalk homomorphism is finite, and that surjectivity of
that same homomorphism yields a closed immersion over an open target
neighborhood, with the whole inverse image as source. There is no field,
Noetherian, rationality, reducedness, unramifiedness or stalk-injectivity premise.

Choose an affine neighborhood `U` of the image point. Its whole inverse image
is affine because the morphism is finite. The lemma
`primesOver_eq_singleton_of_singletonFiber` identifies the primes above the
corresponding target prime as a singleton. The affine-spectrum naturality
square identifies each prime above that target point with a point in the
whole fiber, and injectivity of the source affine open immersion identifies
its prime ideal.

The lemma `finite_stalkMap_of_singletonFiber` uses
`Localization.finite_of_primesOver_eq_singleton` to obtain finiteness between
the corresponding prime localizations. It then uses the arrow isomorphism
`IsAffineOpen.arrowStalkMapIso` to transport that result to the actual stalk
homomorphism `f.stalkMap x`.

For `exists_isClosedImmersion_restrict_of_singletonFiber`, the same arrow
isomorphism transports stalk surjectivity to the induced prime-localization
map. The finite singleton-prime denominator-clearing result
`Langlands.CommutativeAlgebra.exists_awayMap_surjective_of_singleton` supplies
an element outside the target prime at which the canonical away map is
surjective. Its basic open contains the image point. Mathlib's characterization
`IsLocalization.Away.map_surjective_iff` transfers surjectivity to the
localizations given by sections on this basic open, and
`IsAffineOpen.appBasicOpenIsoAwayMap` identifies that map with the scheme's
section map. The isomorphism `arrowResLEAppIso` identifies this section map
with the map on global sections of the whole target restriction. Both source
and target of this restriction are affine, so
`IsClosedImmersion.of_surjective_of_isAffine` yields the claimed closed
immersion. The final theorem pairs this result with finite stalks.

This is an internal derivation from the pinned Mathlib affine-scheme and
localization APIs and the published local-algebra adapter; no
external theorem is transcribed. The adapter's provenance and its extracted
surjectivity argument from Mathlib's stronger bijectivity lemma are described
in its own companion Markdown. No projectivity or ample-existence conclusion
is used here. Independent review and exact-target validation remain necessary
for publication of this proof.
