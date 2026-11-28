# Strictness and the law on scheme-valued points

For a representative `m` on `g : Y ⟶ S`, `IsStrictDomain m` records the six
densities of the domain and the images of `(x,y) ↦ (x,xy)` and `(x,y) ↦ (xy,y)`
over the two projections of `Y ×_S Y`. It expresses the density conditions of
BLR, *Néron Models*, §5.2 Definition 1, p. 115, for the selected representative.

`PairIn` is a range condition on the morphism representing a pair of points over
`S`. `mulPt` lifts a pair in the domain along the domain inclusion and composes
with multiplication. `ldiv` and `rdiv` lift through the two universal translations
and take the missing coordinate. Their equations and cancellation follow from
the monomorphism of each translation. The lemmas also transport the operations
along precomposition and express the associativity of `m` on defined products.
