# Affine coordinates detect homomorphisms to vector groups

This module defines affine coordinates and supplies internal extensionality results for actual group-scheme
homomorphisms into the existing vector group `VectorGroup.groupScheme R n`.
The base `R : CommRingCat.{u}` is any commutative ring, `n` is any natural number,
and the source group scheme `G` is affine over `Spec R`. Neither a field nor
finite type nor commutativity of `G` is assumed.

`VectorGroup.affineCoordinates A x` is the function `Fin n → A` of additive
coordinates of a point of the vector group over an arbitrary affine test algebra
`A : CommAlgCat R`. It is the published corepresented affine-point equivalence
followed by the underlying additive coordinates. It uses no affineness hypothesis
on a source group scheme. `VectorGroup.affineCoordinates_injective` proves that
these coordinates determine the vector-group point.

`VectorGroup.hom_ext_affineCoordinates` says that two homomorphisms are equal
when all coordinates of their values agree on every affine test algebra and
every point over that algebra. These coordinates use
`Corepresented.affinePointsEquiv` for the vector-group functor and its polynomial
corepresentation. The tests include nonreduced algebras.

`VectorGroup.subsingleton_hom_of_affineCoordinates_eq_zero` concludes
`Subsingleton (G ⟶ VectorGroup.groupScheme R n)` from vanishing of every such
coordinate of every such homomorphism. It compares two homomorphisms using the
first result. It does not assert the vanishing premise.

## Provenance and implemented proofs

The definition and its lemmas are internal consequences of the published all-affine-test reconstruction
interface, rather than new statements from the literature.
`AffinePointComparison.hom_ext` detects morphisms with affine source on all
affine points. The vector-group affine point equivalence then reduces equality
of points to equality of their additive coordinate functions, as expressed by
`affineCoordinates_injective`; function extensionality gives that equality. Coordinate vanishing gives coordinate
equality, proving the second result.

The results provide the extensionality step in the proof of Milne's
Proposition 12.54: after proving that every additive character vanishes on every
affine test, the second result with `n = 1` gives uniqueness of additive
characters. This module proves neither the vanishing premise nor that
proposition.
