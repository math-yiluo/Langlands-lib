# Proof: Bruhat–Tits availability from the one-group clauses of corrected Definition 4.1.26

`Langlands.Geometry.Building.bruhatTitsAvailabilityReduction` proves
`BruhatTitsAvailabilityReductionStatement.{u}` for an arbitrary universe `u`.
That statement is the implication

```lean
GroupAxiomsExistenceStatement.{u} → BruhatTitsAvailabilityStatement.{u}
```

The theorem has no premises. It proves the implication only. It assumes neither
`GroupAxiomsExistenceStatement` nor `BruhatTitsAvailabilityStatement`, except
that the first is the antecedent of the implication.

## The implemented proof

Let `h : GroupAxiomsExistenceStatement.{u}`. Then `h F G hG` is an existence
statement `∃ D : KPBuildingDatum G, D.SatisfiesGroupAxioms` for every
nonarchimedean local field `F` in universe `u` and every connected reductive `G`
over `F`.

1. **The assignment.** The proof defines `𝔅 : KPBuildingAssignment.{u}`. Its
   `datum` field sends `F`, `G` and `hG` to `Classical.choose (h F G hG)`. The
   choices for different groups are independent of one another.
2. **Reduction to five clauses.** Fix `F`, `G` and `hG`. By
   `KPBuildingAssignment.isAvailableFor_iff`, `𝔅.IsAvailableFor F G hG` is
   equivalent to five clauses. The first is `SatisfiesGroupAxioms` for the
   assigned datum. The other four are `HasCentralQuotientComparisons`,
   `HasDerivedSubgroupIdentification`, `HasSimplyConnectedCoverIdentification`
   and `HasIsomorphismCompatibility`.
3. **The clauses for `G` alone.** The assigned datum is
   `Classical.choose (h F G hG)`, so `Classical.choose_spec (h F G hG)` gives
   `SatisfiesGroupAxioms`.
4. **The comparisons of Axiom 4.1.1.** The proved theorem
   `buildingComparisonAxiom.{u}`, applied to `F`, is a conjunction of three
   statements. Each one holds for arbitrary `ValuationBuildingData` on both
   sides:
   * central surjections `f : G ⟶ G'`;
   * derived subgroups `d : G_der ⟶ G`;
   * simply connected covers `π : G_sc ⟶ G_der` of a derived subgroup
     `d : G_der ⟶ G`.

   Each comparison clause of `𝔅` uses one of these three components. The proof
   applies it to the groups and morphism of the clause, and to the assigned data
   `𝔅.buildingData` on both sides. The resulting `Φ` and its
   `IsEquivariantBuildingIso` property have exactly the form of the clause.
5. **Axiom 4.1.17.** The proved theorem `isomorphismCompatibilityAxiom` also
   holds for arbitrary valuation data on both sides. Fix `F₂`, a valued-field
   isomorphism `σ : F ≃+* F₂` with `IsValuativeRingEquiv σ`, a connected
   reductive `G₂` over `F₂`, and `fG`. The proof applies the theorem to these
   and to the assigned data of `G` and `G₂`. This gives
   `HasIsomorphismCompatibility`.

The two proved theorems hold for all supplied data. So the choices made for
different groups never have to agree with one another. The assignment `𝔅`
therefore satisfies `IsValid`, which proves `BruhatTitsAvailabilityStatement`.

## Dependencies

* `Langlands.Geometry.Building.BruhatTitsAvailabilityReductionStatement`: the
  target. It imports `GroupAxiomsExistenceStatement` and
  `BruhatTitsAvailabilityStatement`.
* `Langlands.Geometry.Building.BuildingComparisonAxiomProof`
  (`buildingComparisonAxiom`).
* `Langlands.Geometry.Building.IsomorphismCompatibilityAxiomProof`
  (`isomorphismCompatibilityAxiom`).
* `KPBuildingAssignment.isAvailableFor_iff` from
  `Langlands.Geometry.Building.FullValidity.Assignment`.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

This proof follows the route described in the statement's Markdown. KP has no
corresponding numbered result. The mathematical content is in
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023):

* Definition 4.1.26, printed p.165 / PDF p.196, with the authors' corrections
  of 1 November 2024 (PDF p.27).
* Theorem 9.2.7, printed p.329 / PDF p.360.

The proof shows that the comparisons between groups in these axioms follow from
the two proved results for arbitrary data. They therefore impose no further
condition once data with the one-group clauses exist.
