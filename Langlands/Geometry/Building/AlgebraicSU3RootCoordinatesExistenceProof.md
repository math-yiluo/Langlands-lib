# Existence of algebraic SU3 rank-one coordinates at multipliable roots: proof

Module `Langlands.Geometry.Building.AlgebraicSU3RootCoordinatesExistenceProof`.

Worker 5397, for Task 7011 (bd3178b2-02c0-43b9-8b80-4300e506db00).

## The theorem

```
theorem Langlands.Geometry.Building.algebraicSU3RootCoordinatesExistence :
    AlgebraicSU3RootCoordinatesExistenceStatement.{u}
```

It proves the Library statement
`Langlands.Geometry.Building.AlgebraicSU3RootCoordinatesExistenceStatement` at an
arbitrary universe `u`. The statement's Lean file and Markdown are unchanged, and the
theorem has no hypotheses of its own. Here is what the statement says. Take:

- a field `k : Type u` (arbitrary: imperfect fields and characteristic two are allowed);
- a group scheme `G` over `Spec k` with `IsConnectedReductive G`;
- commutative group schemes `S`, `Z` over `Spec k` and morphisms `i : S.toGrp ⟶ G`,
  `j : Z.toGrp ⟶ G`, `s : S.toGrp ⟶ Z.toGrp` such that `i` is a maximal split torus,
  `Z.toGrp` is a torus, `j` represents the subgroup functor `torusCentralizer i`, and
  `s ≫ j = i`;
- an indivisible relative root `b` of `i` such that `2 • b` is also a relative root.

Then there is a record `C : AlgebraicSU3RootCoordinates i j s b` such that `C.rho` maps the
standard SU3 Weyl element `SU3Root.weylElement` (the antidiagonal matrix
`[[0,0,1],[0,-1,0],[1,0,0]]`, bundled with its membership proof) into `normalizerPoints i`.
The record consists of a finite separable field `base` over `k` with a separable quadratic
extension `extension`, unitary root coordinates `RootUnitaryCoordinatesOn` for `b` and `-b`
on that tower, one homomorphism `rho` from the special unitary group to `G(k)` agreeing with
both coordinates, and a morphism `coroot` from the Weil restriction of `𝔾ₘ` along
`extension / k` to `Z` compatible with `rho` on diagonal elements.

## Proof

The proof is one application:

```
algebraicSU3RootCoordinatesExistence_of_product_of_adjacent splitRelativeRootGroupProduct
  Langlands.GroupScheme.adjacentSimpleRootSpecialLinear
```

It uses three published Library results; this module adds no new mathematics.

1. `Langlands.Geometry.Building.algebraicSU3RootCoordinatesExistence_of_product_of_adjacent`
   (module `Langlands.Geometry.Building.AlgebraicSU3RootCoordinatesConstruction`, Worker 163,
   Task 6836) has type
   `SplitRelativeRootGroupProductStatement.{u} → AdjacentSimpleRootSpecialLinearStatement.{u} →
   AlgebraicSU3RootCoordinatesExistenceStatement.{u}`.
   It is the construction of the coordinates. It splits `Z` over a finite Galois extension
   `K` of `k` and takes a root datum over `K`. Then it chooses a generic cocharacter making
   `b` a simple relative root. It assembles the record from the fiber pinning over `b`,
   with base field the pair field and extension the fiber field, and with
   `rho = SplitPinning.unitaryRho`. Finally it proves that the Weyl element maps into
   `normalizerPoints i`. The two propositions are its only hypotheses.
2. `Langlands.Geometry.Building.splitRelativeRootGroupProduct`
   (module `Langlands.Geometry.Building.SplitRelativeRootGroupProductProof`) proves
   `SplitRelativeRootGroupProductStatement.{u}`. Over a field, for a split maximal torus `T`
   of a connected reductive group, a split torus `S` and a homomorphism `S → T`, the
   rational points of the relative root group of a nonzero character `a` of `S` are exactly
   the ordered products of rational points of the absolute root groups over the positive
   multiples of `a`, and the factors are unique.
3. `Langlands.GroupScheme.adjacentSimpleRootSpecialLinear`
   (module `Langlands.GroupScheme.Rational.AdjacentSimpleRootSpecialLinearProof`) proves
   `AdjacentSimpleRootSpecialLinearStatement.{u}`. For simple roots `a`, `b` of a split
   pinning with both pairings equal to `-1`, the rank-one homomorphisms `rootSL2 x a` and
   `rootSL2 x b` are the restrictions of one homomorphism `SL₃(k) →* G(k)` to the two block
   copies of `SL₂(k)`.

Neither proposition is assumed: each hypothesis of the construction is discharged by its
published proof. The proof assumes none of `QuasiSplitValuedRankOneCoordinatesStatement`,
`QuasiSplitR2RootUnitaryCoordinatesStatement` or `QuasiSplitCoordinateApartmentStatement`,
nor any other unproved proposition. `lean_check` of the declaration reports the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Source

The statement is the SU3 case of the proof of Proposition 7.1.1 for quasi-split groups in
Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach* (2023), printed p. 239,
PDF p. 270 (source ID `kaletha-prasad-2023-bruhat-tits-new-approach`). There the group is
reduced to a restriction of scalars of `SL₂` or `SU₃`. The Library statement is an internal,
valuation-free algebraic version over an arbitrary field; its Markdown explains the
provenance. The Lean proof does not follow the source's reduction through the simply
connected cover. It descends explicit split-group constructions from a finite Galois
splitting field, as described in item 1.
