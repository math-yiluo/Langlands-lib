# Transport of supplied outer-isomorphism quotients

This is a derived construction from the Library's all-test universal property
`GroupIsomorphismScheme`, the definition `OuterIsomorphismScheme`, and ordinary
categorical uniqueness of representatives. It does not assert quotient existence.
No external geometric representability result is used.

For group schemes `G,H` over any base scheme `S`, two supplied schemes
representing natural families of isomorphisms are canonically isomorphic:
`GroupIsomorphismScheme.representativeIso I J` classifies `I`'s universal family
in `J`. Classifying in the other direction gives the inverse. The comparison
preserves the universal family on every relative test and intertwines the
canonical inverse-precomposition action of any specified automorphic action on
`G`.

`OuterIsomorphismScheme.changeRepresentative O J` keeps the outer parameter
scheme and precomposes the class morphism with that canonical comparison.
Flatness, surjectivity and quasi-compactness follow by composition with an
isomorphism. Invariance follows from equivariance. For equal-class points,
existence and uniqueness of the acting point transfer by cancellation of the
comparison isomorphism.

`OuterIsomorphismScheme.changeActingGroup O b e he` keeps both the isomorphism
scheme and its class morphism, while replacing the acting group `A` by an
isomorphic group `B`. Its hypothesis identifies `b` with the original action
after `e : B ≅ A` on every relative test. The acting point in `A` supplied by
the original quotient is carried back through `e.inv`; uniqueness follows by
applying `e.hom`. These constructions include nonreduced relative tests and
do not require an acting point to lift through another group scheme.
