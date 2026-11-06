# Cuspidal projections from actual remainder splittings

This internal helper derives projection maps from the supplied
`HasCuspidalRemainderSplitting` of an actual smooth complex representation.
It does not establish that any such splitting exists. Its provenance is the
universal property in that published definition, the actual invariant image,
and the published surjectivity of character localization. It supplies a local
step needed for the finite induced-cuspidal embedding argument.

`boolCoproductTrueProjection` is the actual categorical map to the `true`
component, defined by the coproduct universal property with zero on the
`false` leg and the identity on the `true` leg.

`IsCuspidalFor.of_surjective_intertwiner` preserves cuspidality under a
surjective actual intertwiner with independent source and target carrier
universes. Each normalized Jacquet carrier is the actual localization
quotient; its induced map is surjective and its source is a singleton.

`hom_eq_zero_of_no_cuspidal_subquotient` proves that every map from a
cuspidal object to a representation with no nonzero cuspidal subquotient
vanishes. A nonzero map has a nonzero invariant image in the target carrier
universe. Its range restriction is surjective, so the preceding lemma makes
this image cuspidal, contradicting the stated exclusion.

`HasCuspidalRemainderSplitting.exists_projection` uses the actual Boolean
coproduct to define its two projections by their values on the coproduct
legs. The sum of the two projection-inclusion composites is the identity,
by the coproduct universal property. A map from a cuspidal object has zero
remainder projection by the image argument. If its cuspidal projection is
also zero, the identity formula makes the map zero. The source carrier
universe is independent of the splitting carrier universe.

`HasCuspidalRemainderSplitting.exists_lifted_projection` raises the
cuspidal target carrier by the actual equivariant `ULift` equivalence.
Surjectivity of that equivalence preserves cuspidality; injectivity
preserves the projection's detection property. There is no dimension,
admissibility, irreducibility, or finite-length hypothesis.
