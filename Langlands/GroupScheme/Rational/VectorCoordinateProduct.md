# Actual products of natural vector-coordinate blocks

This internal construction uses a group scheme `V` over an arbitrary field
with the published natural vector coordinates on every test scheme. It
constructs `vectorCoordinateSubgroup e he I`, whose points have zero
coordinates outside the subset `I`, and the actual group-scheme endomorphism
`vectorCoordinateProjection e he I` setting those coordinates to zero.
Naturality follows from the coordinate naturality and pullback of zero.
`range_vectorCoordinateProjection` identifies its range on every test with
the coordinate subgroup.

For a finite family of coordinate subsets in which every coordinate occurs
in exactly one subset, `isIso_orderedMultiplication_vectorCoordinates` proves
that any actual representatives of those subgroups have an isomorphic ordered
multiplication morphism to `V`. The proof evaluates one coordinate at a time.
Only its unique block contributes to the product; all other factors contribute
zero in that additive coordinate. This proves injectivity. Projecting a target
point onto each block and lifting along the representing equivalences supplies
surjectivity. The all-test Yoneda criterion gives an actual scheme isomorphism.
The number of factors and the vector dimension may be zero, and empty blocks
are allowed.

The provenance is internal: natural coordinate masks, multiplication of
finite families, and the represented-subgroup point equivalences suffice.
This supplies vector-coordinate algebra for the weight-decomposition step
in CGP Theorem 3.3.11, printed page 115 (PDF page 141). No identification of
semigroup subgroups with these coordinate blocks, construction of their
representatives, diagonalization of a linear torus action, or full ordered
semigroup product assertion is proved here.
