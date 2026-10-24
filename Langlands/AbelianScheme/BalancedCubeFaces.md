# Coordinate faces of the balanced cube tensors

This internal construction joins the actual right-associated product and face
maps in `FieldCubeTrivialityStatement` to the tensors in `BalancedCubeFactors`.
The base `S` is any scheme, and `G` is any group object in `Over S`. No field,
commutativity, smoothness, properness or connectedness is assumed here.

The abbreviation `cube G` is `G.X ⨯ (G.X ⨯ G.X)`. Its three coordinate maps
are the first projection, the second projection followed by the first, and the
second projection followed by the second. `cubePositive` and `cubeNegative`
substitute these coordinate maps into the already defined four-factor and
three-factor tensors, preserving their exact parenthesizations and factor order.

Each of `firstFace`, `secondFace`, and `thirdFace` is the corresponding published
`CubeFace` map, with the rational section chosen as the unit element in
`Over.mk (𝟙 S) ⟶ G.X`. Thus their three coordinates are respectively
`(1, fst, snd)`, `(fst, 1, snd)`, and `(fst, snd, 1)`.
The universal properties of the binary products and `MonObj.comp_one` establish
these identities.

Each face comparison requires two explicit inputs:

- `preservation : pullbackTensorComparisonIsIsoStatement`, the invertibility
  of the canonical pullback-tensor comparison for all scheme maps at this universe;
- an actual isomorphism between the constant identity pullback of `L` on
  `(G.X ⨯ G.X).left` and its structure sheaf.

The construction first uses `pullPositiveIso` to distribute pullback and compose
the coordinate maps. It then uses the corresponding `firstUnitIso`,
`secondUnitIso`, or `thirdUnitIso`, and ends with the inverse of
`pullNegativeIso`. The result is an actual isomorphism between the two tensor
restrictions along the published cube face. It does not assert triviality of
either individual face restriction.

For any `T : Over S` and three maps `f,g,h : T ⟶ G.X`, `tripleMap` is the
product lift `(f,(g,h))`. The construction `pullCubeIso` takes an actual
isomorphism `cubePositive G L ≅ cubeNegative G L` and the same tensor-preservation
input. It pulls that isomorphism back along `tripleMap` and composes with the
positive and negative pullback comparisons, obtaining
`positive G L f g h ≅ negative G L f g h`. No geometric condition on `T`
is needed.

These are derived categorical constructions from the published product,
pullback and tensor comparisons. Their intended application is the face
calculation in Milne, *Abelian Varieties*, Corollary 6.4 and the functorial
pullback argument in the proof of Corollary 6.5, printed/PDF p.9, retained
author revision of January 2, 2022. The factor signs follow Corollary 6.4;
Corollary 6.5's displayed formula omits an inverse on `(f+h)^*L`.
This module describes the categorical portion of that argument, not a
geometric cube theorem over arbitrary base schemes.

The tensor-preservation proof, the field-fibre trivialization, and existence of
the global cube comparison remain separate obligations. In particular,
`pullCubeIso` explicitly assumes the comparison on the triple product and does
not prove `FieldCubePullbackStatement`.
