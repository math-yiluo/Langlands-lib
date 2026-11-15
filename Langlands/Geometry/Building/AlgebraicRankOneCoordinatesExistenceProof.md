# Existence of coherent algebraic rank-one coordinates: proof

Module `Langlands.Geometry.Building.AlgebraicRankOneCoordinatesExistenceProof`.

Workers 163 and 195, for Task 6836 (8c04a3ed-3fa6-4680-a59f-856738cb578b).

## Statement

`theorem Langlands.Geometry.Building.algebraicRankOneCoordinatesExistence :
AlgebraicRankOneCoordinatesExistenceStatement.{u}`, at an arbitrary universe `u`. The type is
exactly the published proposition of module
`Langlands.Geometry.Building.AlgebraicRankOneCoordinatesExistenceStatement`. Let `G` be
connected reductive over a field `k`, `i : S → G` a maximal split torus, `j : Z → G` a torus
representing the torus centralizer of `i`, and `s ≫ j = i`. Then every indivisible relative
root `b` has algebraic `SL₂` coordinates (when `2 • b` is not a relative root) or algebraic
`SU₃` coordinates (when it is). In both cases the standard Weyl element maps into
`normalizerPoints i`. This is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Proposition 7.1.1 (printed p. 239), in the algebraic form fixed by that statement.

## Proof

The proof is one application:

`algebraicRankOneCoordinatesExistence_of_adjacent adjacentSimpleRootSpecialLinear`.

- `Langlands.GroupScheme.adjacentSimpleRootSpecialLinear :
  AdjacentSimpleRootSpecialLinearStatement.{u}` (module
  `Langlands.GroupScheme.Rational.AdjacentSimpleRootSpecialLinearProof`, Worker 195) gives,
  for adjacent simple roots `a, b` of a split pinning, a homomorphism `SL₃(k) →* G(k)` whose
  two block restrictions are the rank-one homomorphisms of `a` and `b`.
- `algebraicRankOneCoordinatesExistence_of_adjacent` (module
  `Langlands.Geometry.Building.AlgebraicSU3RootCoordinatesConstruction`) derives the target
  from that statement. It combines two results:
  - `algebraicRankOneCoordinatesExistence_of_product_of_su3` (module
    `AlgebraicSL2RootCoordinatesConstruction`), which proves the `SL₂` clause and reduces the
    target to `SplitRelativeRootGroupProductStatement` and the `SU₃` clause;
  - the published proof `splitRelativeRootGroupProduct` of the product statement (module
    `SplitRelativeRootGroupProductProof`), together with
    `algebraicSU3RootCoordinatesExistence_of_product_of_adjacent`, which proves the `SU₃`
    clause from the product statement and the adjacent-root statement.

The construction behind these modules is described in their Markdown files:
`SimpleRootFiberPinning`, `SimpleRootFiberCoordinates`, `SimpleRootFiberCoroot`,
`SimpleRootFiberProducts`, `OrthogonalOrbitWeylNormalizer` for `SL₂`;
`SimpleRootFiberPartners`, `PartnerOrbitSpecialUnitary`, `PartnerOrbitUnitaryCoordinates`,
`PartnerOrbitRootProducts`, `SimpleRootFiberUnitary` for `SU₃`.

`#print axioms` gives `propext`, `Classical.choice`, `Quot.sound`.
