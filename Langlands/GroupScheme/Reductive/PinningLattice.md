# Actual torus lifts for pinned root data

Author: Worker 1467.

This internal construction is derived from the published actual character-map
construction in `Torus.CharacterMapHom`, character separation in
`Torus.CharacterIsomorphism`, pairing invariance in `Torus.LatticeGalois`,
and Mathlib's transpose equation for equivalences of root pairings. It does
not assert a new result from an external source.

`IsSplitTorus.isoOfCharacterEquiv` realizes a forward additive equivalence
between the full character lattices of two split tori over a domain. Its
forward homomorphism is the published homomorphism whose character pullback
is the inverse equivalence, and its inverse realizes the forward
equivalence as pullback. Character separation proves that the two composites
are identities. Consequently inverse character pullback along this actual
torus isomorphism is precisely the given equivalence. Character separation
also shows that this equation determines the complete torus isomorphism.

For supplied actual pinnings `p` and `q` over any field, and an equivalence
`e` of their full root data, `SplitPinning.torusIsoOfRootDatumEquiv`
applies this construction to `e.weightEquiv`. Its forward character map
is exactly `e.weightEquiv`, as an integral linear equivalence.

`cocharacter_congr_eq_of_character_congr` proves, for any actual torus
isomorphism with that character equation, that its forward cocharacter map
is `e.coweightEquiv.symm`. To prove equality of two cocharacters, the proof
uses injectivity of the target root datum's perfect pairing and tests
against all target characters. Every target character is `e.weightEquiv ψ`.
Invariance of the actual torus pairing and the transpose equation for `e`
give equal pairings with the two cocharacters. The root-data realization
equations identify the root-data pairings with the actual lattice pairings.

The resulting torus isomorphism carries every root and coroot to the index
specified by `e.indexEquiv`, using the root and coroot equations of `e`.
`existsUnique_torusIso_of_rootDatumEquiv` packages uniqueness of the actual
torus isomorphism with both full lattice equations.

All character and cocharacter lattices are the full integral lattices of
the supplied actual tori. No root-span restriction or nonempty-root
assumption occurs. The field and universe are arbitrary. These results
construct only the torus component of a possible pinned isomorphism.
Extension to an actual group isomorphism, compatibility with the supplied
simple-root vectors, and faithfulness on the whole group remain separate
obligations of `PinnedIsomorphismStatement`.
