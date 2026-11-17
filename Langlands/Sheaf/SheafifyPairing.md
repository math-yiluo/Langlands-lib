# Extending natural pairings through local bijections

This internal helper constructs the extension of a natural pairing through two
locally bijective maps of presheaves of types on an arbitrary site. It prepares
the construction of composition on the sheaf of rational formal homomorphisms.
No original-literature theorem is asserted.

`pairs P Q` has pairs of sections on each object and componentwise restriction;
`pairsMap f g` applies the two given natural transformations. If both maps are
locally injective, their pair map is locally injective: the intersection of the
two covering equalizer sieves is contained in the equalizer sieve for pairs.
If both are locally surjective, their pair map is locally surjective: the
intersection of their two covering image sieves is contained in the image
sieve for pairs, by pairing local preimages.

Assume the site's class `W` agrees with locally bijective maps of presheaves
of types in the chosen universe. This is the explicit
`WEqualsLocallyBijective` hypothesis. Given a sheaf `H` and a natural pairing
`b : pairs P Q ⟶ H.obj`, `extend` is the inverse image of `b` under the
bijection on morphisms into `H` induced by `pairsMap f g`. That bijection is
the defining universal property of `W`, whose hypothesis follows from the
two preceding local calculations.

`pairsMap_extend` and `extend_apply` prove agreement with the original pairing.
`extend_unique` proves that this agreement determines the extension. The helper
does not impose or assert additivity, bilinearity, associativity, or identity
laws; these can be checked separately for the pairing being extended.
