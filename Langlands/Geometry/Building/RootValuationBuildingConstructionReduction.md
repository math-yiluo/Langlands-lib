# The actual quotient and its five axiom families, from four structural statements

This derived unit reduces the published target
`RootValuationBuildingConstructionStatement` to four Prop-valued statements, all at
the same universe `u`:

- `ValuationApartmentAxiomsExistenceStatement`: for every connected reductive `G`
  over a nonarchimedean local field there is `B : ValuationBuildingData G` with
  `B.SatisfiesApartmentAxioms` (KP Theorem 9.6.5 with §9.5 and 9.6.6);
- `ActualApartmentSplittingStatement`: actual data satisfying these axioms carry an
  apartment splitting satisfying KP Axiom 4.1.4;
- the published `AffineIwahoriTitsStatement`: the `G(F)^0` branch of KP Theorem
  7.5.3(1),(2) at every chamber, under the same apartment axioms;
- `AffineIwahoriTitsBuildingStatement`: that Iwahori–Tits system is the Tits system
  of KP Axiom 4.1.9 on the existing quotient `B(G)` (KP Propositions 7.6.3 and
  7.6.4(1), Remark 7.6.5).

## Statement

```text
def RootValuationBuildingConstructionReductionStatement : Prop :=
  ValuationApartmentAxiomsExistenceStatement.{u} →
    ActualApartmentSplittingStatement.{u} →
      AffineIwahoriTitsStatement.{u} →
        AffineIwahoriTitsBuildingStatement.{u} →
          RootValuationBuildingConstructionStatement.{u}
```

The theorem `rootValuationBuildingConstructionReduction` proves it. The four
antecedents are explicit; this unit proves none of them and does not prove the
target outright. The target is unchanged: its field, group and connected-reductivity
hypotheses are introduced exactly as stated, and the conclusion is the target's own
seven predicates on the constructed `P`, a realization `R` and a splitting `T`.

## Proof

`ParahoricBuildingData.exists_toValuationBuildingData_eq` extends any
`B : ValuationBuildingData G` to `P : ParahoricBuildingData G` with
`P.toValuationBuildingData = B`. It takes a simply connected derived cover of `G`
from the proved `simplyConnectedDerivedCoverExistence`. The centralizer `Z = Z_G(S)`
of `B` is connected reductive (`isConnectedReductive_centralizer`), and so is its base
change to the maximal unramified extension `UnramifiedClosure F`, an algebraic
extension (`IsConnectedReductive.baseChange_of_algebraicExtension`). A second
application of `simplyConnectedDerivedCoverExistence` gives the cover of that base
change. The existing constructor `ParahoricBuildingData.ofDerivedCovers` assembles
`P` without changing `B`, so the apartment, valuations, quotient and
`rationalPoints` action are those of `B`.

`ParahoricBuildingData.fiveAxioms_of_statements` proves the seven predicates for
such `P` from `hD : P.SatisfiesApartmentAxioms`, a splitting witness, and the two
Iwahori–Tits statements.

- A chamber: AS 3 makes `P.affineRoots` a locally finite reflection arrangement,
  which has a regular point `x` (`exists_regularPoint`); its facet `Ca` is a chamber.
- At `Ca`, `AffineIwahoriTitsStatement` gives normality of `P.normalizerZero` and
  `P.zeroSubgroup` and `e` with `P.AffineIwahoriTitsWith Ca e`;
  `AffineIwahoriTitsBuildingStatement` turns these into
  `hB : P.IsBuildingTitsSystem Ca P.affineTitsProjection (P.chamberSimpleInAffinePart e Ca)`.
- Axiom 4.1.1: `R = hB.titsRealization`, the published restricted-building
  realization, and `satisfiesBuildingAxiom_affineTitsRealization_of_statements` with
  the proved `simplyConnectedCentralizerProduct` and `maximalSplitTorusConjugacy`.
- Axiom 4.1.2: `hasBoundedOpenStabilizers_of_rankOne_and_isOpen` with the proved
  rank-one factorization `hasRankOneFactorization_actual`, the proved
  `RelativeRoot.openRootCentralizerGeneration` and openness of `Z(F)^0` from the
  proved `centralizerZeroCompactOpen`.
- Axiom 4.1.4: the supplied splitting `T` and its witness.
- Axiom 4.1.6: AS 1 is `RootReflectionProof.hasRootReflections`, the Chapter 7
  apartment axioms are `hD`, and AS 6 is `hasCompatibleApartmentFacets_of_rankOne`.
- Axiom 4.1.9: for every chamber `Ca'`, the two statements give normality, `e'` and
  `P.IsBuildingTitsSystem Ca' P.affineTitsProjection (P.chamberSimpleInAffinePart e' Ca')`;
  the Weyl group is `P.affinePart`, which lies in `Type u`.

`rootValuationBuildingConstructionReduction` introduces the target's hypotheses,
obtains `B` and `hD` from the first antecedent, extends `B` to `P`, obtains the
splitting from the second antecedent applied to `P.toValuationBuildingData` and
`hD`, and applies `fiveAxioms_of_statements`.

## Provenance

The proposition is an implication between unchanged published Library statements
and three new statements, all at universe `u`. It mirrors the source route: KP
4.1.28 (printed p. 166 / PDF p. 197) records that once valuations of root data are
available (§9.6), the material of Chapters 6 and 7 applies to every `G`; in Chapter 7,
Theorem 7.5.3 constructs the Iwahori–Tits system and Propositions 7.6.3 and 7.6.4 with
Remark 7.6.5 (printed pp. 264–266 / PDF pp. 295–297) complete the proofs of Axioms
4.1.1, 4.1.4 and 4.1.9 on the quotient (7.6.2). No object, convention or hypothesis is
introduced; the proof assembles published adapters and proved theorems.
