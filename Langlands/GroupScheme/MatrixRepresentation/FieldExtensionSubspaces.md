# Scalar extension of actual stable subspaces

This internal subspace interface supports part (a) of Milne, *Algebraic Groups*
(2017), Proposition 4.19, pp. 90–91 (`milne-2017-algebraic-groups`).
`FieldExtensionSubspaces.scalarExtension` is the new-field span of the
entrywise images of the original vectors.

Split invariant coordinates and actual intertwiners extend by applying the field
map entrywise. Their proofs use the actual point-matrix base-change comparison
and the compatibility of structure-ring maps. An original stable subspace has
finite split inclusion coordinates; its extension is the range of the extended
inclusion matrix and is therefore stable under the actual extended representation.

Every ground-field linear coefficient of a vector in the extended subspace lies
in the original subspace. The proof uses span induction; in the scalar step the
coefficient functional is precomposed with multiplication by that scalar. A
linear functional on the extension field taking one to one shows that membership
of original vectors is reflected. The bottom-or-top dichotomy after extension
therefore descends, proving `IsIrreducible.of_baseChange`.

All results retain the Library's all-affine-test stability and intertwining
predicates and hold for arbitrary affine group schemes over fields.

The scalar-extension definition delegates to the definitionally identical
`GaloisPiDescent.scalarExtension`. Coefficient extraction,
`Intertwines.baseChange` and `IsStableSubspace.scalarExtension` reuse the
published `ScalarExtensionStableSubspaces` and `ScalarExtensionCoordinates`
interfaces. Membership reflection retains its arbitrary-coordinate-type scope.
