# Actual coinvariants of finite products

This internal algebraic construction identifies the actual quotient of a finite
dependent product with the product of the actual coinvariant quotients.
The finite index, group, and coefficient universes are independent. The complex
coefficient modules may have arbitrary dimension, and no topology or smoothness
assumption enters the construction.

For a family of representations `ρ j` and a subgroup `N`, the forward map sends
the class of a family `x` to the family of classes of `x j`.
`coinvariantsToProduct` descends the product of coordinate quotient maps, since
each coordinate quotient kills its actual relations `ρ j n v - v`.
This direction does not require a finite index.

For the inverse, a coordinate inclusion `Pi.single j` intertwines the coordinate
representation with the pointwise product representation. Its composite with
the product quotient map descends to `coordinateToCoinvariants`.
`productToCoinvariants` sums these descended maps over the finite index.
The finite decomposition of a family as the sum of its coordinate inclusions
proves `productToCoinvariants_mk`. Surjectivity of the actual quotient maps
then proves both inverse identities. The inverse construction uses no choice
of quotient representatives; representatives are used only in the proof of
the inverse identities. This also treats an empty finite index.

`coinvariantsEquiv` is the resulting canonical complex linear equivalence.
Its representative formula is `coinvariantsEquiv_mk`.

For a standard block shape `C` over any commutative ring, `jacquetEquiv`
combines this equivalence with the published equivalence between the parabolic
Jacquet quotient and the coinvariants of the ambient unipotent subgroup.
It sends `C.jacquetMk` of a family to the family of coordinate `C.jacquetMk`
classes. `jacquetEquiv_intertwining` proves that it intertwines the actual
normalized Levi actions for any supplied full positive modulus: the same
inverse square root multiplies every coordinate, and the actual embedded
Levi action acts coordinatewise.

The provenance is internal: the actual quotient universal property, finite
coordinate decomposition, and the published standard parabolic representative
formulas prove these assertions. No geometric filtration, orbit integral,
complex exactness, or Aubert effectivity theorem is assumed or proved here.
