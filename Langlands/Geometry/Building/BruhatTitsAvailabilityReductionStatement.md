# Bruhat–Tits availability from the one-group clauses of corrected Definition 4.1.26

`Langlands.Geometry.Building.BruhatTitsAvailabilityReductionStatement` is the
proposition

```lean
GroupAxiomsExistenceStatement.{u} → BruhatTitsAvailabilityStatement.{u}
```

for an arbitrary universe `u`. It states the implication only: it asserts
neither its premise nor its conclusion.

## The two sides

* The premise, `GroupAxiomsExistenceStatement`, says that for every connected
  reductive group `G` over every nonarchimedean local field `F` in universe `u`
  there is a datum `D : KPBuildingDatum G` with `D.SatisfiesGroupAxioms`. These
  are the clauses of the ten axioms of corrected KP Definition 4.1.26 that
  concern `G` alone: Axiom 4.1.1 for `G` alone and Axioms 4.1.2, 4.1.4, 4.1.6,
  4.1.8, 4.1.9, 4.1.16, 4.1.20 and 4.1.22. The data for different groups are
  chosen independently.
* The conclusion, `BruhatTitsAvailabilityStatement`, says that some
  `𝔅 : KPBuildingAssignment.{u}` satisfies `𝔅.IsValid`. In that case
  `𝔅.IsAvailableFor F G hG` holds for every such `G` over `F`. This is all ten
  corrected axioms of Definition 4.1.26, including the comparisons between
  groups. These comparisons are the central-quotient comparisons and the
  `G_der` and `G_sc` identifications of Axiom 4.1.1, and Axiom 4.1.17. Axiom
  4.1.27 (unramified descent) is not part of either side.

So the proposition says that the comparisons between groups add nothing once
data with the one-group clauses exist for every group.

## Why it is expected to hold

The Library already has two relevant decompositions:

* `KPBuildingAssignment.isAvailableFor_iff` splits `IsAvailableFor` into
  `SatisfiesGroupAxioms` for the assigned datum, plus four comparison clauses.
* The proved statements `BuildingComparisonAxiomStatement`
  (`buildingComparisonAxiom`) and `IsomorphismCompatibilityAxiomStatement`
  (`isomorphismCompatibilityAxiom`) assert these comparison clauses for
  arbitrary supplied valuation data on both sides.

Therefore an assignment that chooses, for each group, any datum supplied by the
premise is expected to satisfy `IsValid`. This paragraph describes the expected
route only. The Markdown records no proof, and this module contains none.

## Provenance

This is an internal assembly statement of the Library's split of
`BruhatTitsAvailabilityStatement`; KP has no corresponding numbered result. Its
mathematical source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023):

* Definition 4.1.26, printed p.165 / PDF p.196. The authors' corrections of
  1 November 2024 (PDF p.27) replace its list of axioms by "Axioms 4.1.1,
  4.1.2, 4.1.4, 4.1.6, 4.1.8, 4.1.9, 4.1.16, 4.1.17, 4.1.20, and 4.1.22".
* Theorem 9.2.7, printed p.329 / PDF p.360. Its availability conclusion is the
  target of `BruhatTitsAvailabilityStatement`.
