# Smoothness of represented fppf products over a field

This internal derived module proves smoothness of an existing represented
fppf product. It constructs no representative. Both the field and all schemes
lie in an arbitrary universe `u`; there is no perfectness, characteristic,
connectedness, or smoothness assumption on the ambient group.

`Langlands.GroupScheme.smooth_of_epi_from_smooth` concerns a group scheme `P`
over a field. Its structure morphism is affine and locally of finite type. A
morphism `q : V ⟶ P.X` from a smooth affine relative scheme is assumed to be
an epimorphism on the underlying schemes. The morphism need not be a group
homomorphism, and `V` need not carry a group structure.

Smoothness makes `V` geometrically reduced by the published
`SmoothReducedProof.geometricallyReduced_of_smooth`. Affineness of the two
schemes allows the published
`SchemeImageGeometry.geometricallyReduced_of_epi` to descend geometric
reducedness along `q`. Mathlib's `AlgebraicGeometry.smooth_of_grpObj` then makes
the geometrically reduced group `P` smooth. That theorem works over every
field: it proves the result after passage to an algebraic closure, using
translations and the dense smooth locus, and descends smoothness. The present
proof imports and applies it directly.

`SubgroupFunctor.IsFppfProduct.smooth` applies this result to the actual
multiplication map supplied by `FppfProductGeometry`. Its assumptions are an
existing represented fppf product, representations of its two factors by
smooth affine group schemes `H` and `N`, and affineness and local finite type
of the product representative `P`. The scheme `H × N` is smooth and affine.
The published `IsFppfProduct.epi_productMul` makes its multiplication map to
`P` an epimorphism, giving the conclusion.

The proposition `IsFppfProduct` retains its existing membership equivalence
on every relative scheme test, including nonaffine and nonreduced tests.
No factorization over the original test scheme is assumed here. For a
closed product representative in an affine group of locally finite type,
the assumptions on `P` follow by composition of its closed immersion with
the ambient structure morphism. The same observation supplies affineness
of closed factor representatives.

These are internal consequences of the named published Library results and
Mathlib's group-scheme smoothness theorem. No additional representability
theorem or external source assertion is introduced.
