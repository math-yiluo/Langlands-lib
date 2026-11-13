# The one-group clauses of corrected Definition 4.1.26 from four focused statements

`Langlands.Geometry.Building.GroupAxiomsExistenceReductionStatement` is the
proposition

```lean
RootValuationBuildingConstructionStatement.{u} →
  RootGroupActionAxiomStatement.{u} →
    IwahoriDecompositionAxiomStatement.{u} →
      IntegralModelAxiomsStatement.{u} →
        GroupAxiomsExistenceStatement.{u}
```

for an arbitrary universe `u`. It states the implication only: none of the five
statements is asserted.

## The premises and the conclusion

All five statements quantify over every nonarchimedean local field `F` in
universe `u` and every group scheme `G` over `F`.

1. `RootValuationBuildingConstructionStatement` covers every connected
   reductive `G`. It asserts that there exist `P : ParahoricBuildingData G`, a
   polysimplicial realization `R` and an apartment splitting `T` satisfying
   seven predicates: `SatisfiesBuildingAxiom R`, `HasBoundedOpenStabilizers`,
   `SatisfiesAffineApartmentAxiom T`, `HasRootReflections`,
   `SatisfiesApartmentAxioms`, `HasCompatibleApartmentFacets` and
   `HasTitsSystem`. These predicates express Axioms 4.1.1 (for `G` alone),
   4.1.2, 4.1.4, 4.1.6 and 4.1.9.
2. `RootGroupActionAxiomStatement` takes any `P` with `SatisfiesApartmentAxioms`
   (V 7 and AS 2–AS 5). It asserts `HasZeroFixerGenerators` and
   `HasRootZeroFixers`, which are Axiom 4.1.8 (2) and (3).
3. `IwahoriDecompositionAxiomStatement` takes any `P` with
   `SatisfiesApartmentAxioms`. It asserts `HasIwahoriDecomposition`, which is
   Axiom 4.1.16.
4. `IntegralModelAxiomsStatement` takes any `P`, `R`, `T` satisfying the seven
   predicates of item 1. It asserts that there exist integral models `M`,
   special-fibre quotients `Q` and relative root reflection data `ρ` with
   `M.SatisfiesModelAxioms P` (Axiom 4.1.20) and `Q.SatisfiesMorphismAxioms ρ`
   (Axiom 4.1.22).

The conclusion, `GroupAxiomsExistenceStatement`, covers every connected
reductive `G`. It asserts that there is `D : KPBuildingDatum G` with
`D.SatisfiesGroupAxioms`: Axiom 4.1.1 for `G` alone and Axioms 4.1.2, 4.1.4,
4.1.6, 4.1.8, 4.1.9, 4.1.16, 4.1.20 and 4.1.22.

## Why it is expected to hold

The fields of `KPBuildingDatum.SatisfiesGroupAxioms` match the hypotheses and
conclusions of the four premises one by one, as follows:

* the predicates for Axioms 4.1.1, 4.1.2, 4.1.4, 4.1.6 and 4.1.9 come from
  premise 1;
* Axiom 4.1.8 (1) holds for all data
  (`KPBuildingDatum.satisfiesRootGroupActionAxiom_iff`), and (2)–(3) come from
  premise 2;
* Axiom 4.1.16 comes from premise 3;
* Axioms 4.1.20 and 4.1.22 come from premise 4.

This describes the expected route only. The Markdown records no proof, and this
module contains none.

## Provenance

This is an internal assembly statement of the Library's split of the one-group
clauses of Definition 4.1.26 into focused statements; KP has no corresponding
numbered result. Its mathematical source is Kaletha–Prasad, *Bruhat–Tits Theory:
A New Approach* (2023), Definition 4.1.26, printed p.165 / PDF p.196, in the form
fixed by the authors' corrections of 1 November 2024 (PDF p.27): "Axioms
4.1.1, 4.1.2, 4.1.4, 4.1.6, 4.1.8, 4.1.9, 4.1.16, 4.1.17, 4.1.20, and 4.1.22
hold". The source of each premise is recorded in its own Markdown file.
