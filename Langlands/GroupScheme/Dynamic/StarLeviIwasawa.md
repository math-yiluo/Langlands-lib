# Levi-compatible Iwasawa from simultaneous star realization

This internal construction by Worker 1655 reduces the actual local
Levi-compatible Iwasawa construction to simultaneous star realization of
the ambient group and a specified dynamic Levi. Coefficients form an
arbitrary-universe `RCLike` field. The file proves a conditional construction;
it leaves existence of simultaneous realization for an arbitrary reductive
group and supplied rational Levi open.

## Normality from the represented centralizer

`affineMatrix_cocharacterPointHom_eq_cocharacterUnitsHom` identifies the
matrix of an actual scalar-unit cocharacter point with the actual matrix
cocharacter obtained by composition with the representation. This is
associativity of actual scheme morphisms under the two affine-point
coordinate definitions.

`isStarNormal_cocharacterUnitsHom_of_centralizer_star_stable` assumes an
actual morphism `m : M ⟶ G` represents the dynamic centralizer of a
cocharacter `χ`, and the point image of the restricted representation
`ρ.restrict m` is stable under conjugate transpose. No closedness or
affineness hypothesis is needed for this lemma.

For any scalar unit `t`, the point `χ(t)` belongs to the centralizer:
the published `range_le_centralizer` states this on all test schemes.
Representability gives an actual lift `x` in `M`. Restricted star
stability supplies an actual point `y` of `M` whose represented matrix
is the conjugate transpose of the represented matrix of `x`. Since
`y` maps into the centralizer, its image commutes with `χ(t)`.
Mapping this commutation through the representation and then to the
underlying matrices proves normality of the matrix `χ(t)`.

`hasNormalPositivePoint_of_centralizer_star_stable` specializes the
result to the positive scalar two. The imported normal-weight theorem
therefore makes every Laurent weight projector Hermitian.

## The simultaneous realization predicate

`HasStarLeviRealization p m` asserts existence of a finite-dimensional
actual matrix representation `ρ` and an actual cocharacter `χ` such that:

- `ρ` is a closed immersion;
- the specified morphism `p` represents the dynamic parabolic of `χ`;
- the specified morphism `m` represents its dynamic centralizer;
- the ambient and restricted-Levi matrix point images are both stable
  under conjugate transpose.

Both stability conditions concern actual base-field point ranges. The
two representation conditions concern subgroup functors on every test
scheme. No compact subgroup or decomposition is part of these data.

`hasHermitianStarLeviRealization` keeps the same representation,
cocharacter and supplied subgroup morphisms, and supplies the missing
Hermitian projectors by the preceding normality argument.
`hasDiagonalStarLeviRealization` then invokes the imported unitary
diagonalization bridge.

With ambient affineness, `hasLeviCompatibleDecomposition` applies the
existing diagonal polar construction. Its output is a compact subgroup
maximal among compact subgroups of the actual ambient affine-point
group, ordered coverage by the parabolic image times that compact,
equality of the intersections of the supplied parabolic and Levi images
with that compact, and maximal compactness of its inverse image on the
actual Levi point group. Each carrier uses its own regular-function
evaluation topology.

The provenance is the implemented centralizer commutation argument and
the imported Laurent-weight, unitary diagonalization and polar
constructions. This file does not prove the full archimedean existence
statement: a common cocharacter for the prescribed pair and a simultaneous
star-stable closed representation still have to be constructed.
