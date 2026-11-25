# Existence of valued unitary coordinates of multipliable root groups: proof

Module `Langlands.Geometry.Building.MultipliableRootGroupCoordinatesExistenceProof`.

## The theorem

```
theorem Langlands.Geometry.Building.multipliableRootGroupCoordinatesExistence :
    MultipliableRootGroupCoordinatesExistenceStatement.{u}
```

It proves the Library statement
`Langlands.Geometry.Building.MultipliableRootGroupCoordinatesExistenceStatement` (module
`MultipliableRootGroupCoordinates`) at an arbitrary universe `u`. The theorem has no hypotheses
of its own, and the statement pair is unchanged. The statement says the following. Let `F` be a
nonarchimedean local field, `K = inertiaFixedField F` its maximal unramified field, `G` an
affine group scheme over `K` with building data `B : MaximalUnramified.BuildingData F G`, and
`b` a relative root of `B.i` such that `2 • b` is also a relative root. Then there is a record
`ValuedUnitaryRootGroupCoordinates B b`. Such a record consists of:

- a finite separable extension `E / K` and a separable quadratic extension `L / E`;
- a homomorphism of group schemes `R_{E/K} U_{L/E} ⟶ G` representing the root subgroup of `b`;
- a point of the apartment at which the root valuation of every unitary parameter
  `(u, v)` is its tower depth.

## Proof

The proof is a single application of three published theorems:

```
multipliableRootGroupCoordinatesExistence_of_algebraicSU3
  algebraicSU3RootCoordinatesExistence
  Langlands.GroupScheme.RelativeRoot.unitaryChartUpgrade
```

- `multipliableRootGroupCoordinatesExistence_of_algebraicSU3` (module
  `MultipliableRootGroupCoordinatesReduction`) derives the statement from two hypotheses:
  `AlgebraicSU3RootCoordinatesExistenceStatement` and `UnitaryChartUpgradeStatement`. Its
  Markdown gives the construction. Coherent SU3 coordinates `C` with Weyl normalization give
  rational unitary coordinates `φ` of the root group `U_b`. Split coroot points give scaling by
  every `c ∈ Kˣ`. `HeisenbergNormalForm.exists_unitaryChartForm` (module
  `RootHeisenbergUnitaryChartForm`) shows that `φ` has chart form. The upgrade statement turns
  `φ` into a scheme homomorphism. The depth condition comes from `coordinateOrigin_depths`
  (module `ValuedSU3CoordinateAssembly`).
- `algebraicSU3RootCoordinatesExistence` (module `AlgebraicSU3RootCoordinatesExistenceProof`)
  proves `AlgebraicSU3RootCoordinatesExistenceStatement`.
- `Langlands.GroupScheme.RelativeRoot.unitaryChartUpgrade` (module
  `Langlands.GroupScheme.Examples.SU3RootUnitaryChartUpgrade`) proves
  `UnitaryChartUpgradeStatement` (module `RootHeisenbergUnitaryChart`).

No other premise is assumed. The theorem depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.
