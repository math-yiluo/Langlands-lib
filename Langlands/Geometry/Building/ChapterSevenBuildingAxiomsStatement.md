# The Chapter 7 building of supplied valuation data satisfies the Section 4.2 axioms

`Langlands.Geometry.Building.ChapterSevenBuildingAxiomsStatement` is a
Prop-valued `def` at every universe `u`. It states the main output of
Kaletha–Prasad Chapter 7 for the Library's building of supplied valuation
data: under the corrected Chapter 7 hypotheses, that building carries a
polysimplicial structure and an apartment splitting for which the axioms of
the corrected opening of KP Section 4.2 hold. The module supplies no proof.

## Statement

The proposition quantifies over:

- every nonarchimedean local field `F`, of either characteristic;
- every group scheme `G` over `Spec F` with `[IsAffineHom G.X.hom]`;
- every `P : ParahoricBuildingData G`. These are the Library's building data:
  a maximal split torus `i : S → G`, the class `A(S)` of valuations of the
  root datum of `(G, S)` normalized by the valuation of `F`, the actual
  centralizer `Z = Z_G(S)` with axiom V 6 on `Z(F)`, and the data of KP
  Definition 2.6.23 for `Z(F)^0` and `G(F)^0`. Connected reductivity of `G`
  is a field of the data.

Its single premise is `P.SatisfiesApartmentAxioms`, which unfolds to
`P.apartment.SatisfiesApartmentAxioms P.centralizer`. Since V 6 is part of
the data, the premise asks for V 7 (the root filtrations are compatible with
the topology of `G(F)`, KP Definition 6.1.2) and AS 2–AS 5 of KP Axiom 4.1.6.

The conclusion asserts that there are a polysimplicial structure
`R : P.toValuationBuildingData.PolysimplicialRealization` on the existing
quotient `B(G) = P.toValuationBuildingData.ReducedBuilding` and an apartment
splitting `T : P.toValuationBuildingData.ApartmentSplitting` such that:

1. `P.SatisfiesBuildingAxiom R`: KP Axiom 4.1.1 for `G` alone. The face
   relations of `R` and `B(G)` agree, `R` with its apartments is a building
   (KP Definition 1.5.5), `G(F)` acts by polysimplicial automorphisms,
   apartments correspond bijectively and equivariantly to maximal split tori,
   and the stabilizer of `A(S)` in `G(F)` is `N(F)`;
2. `P.HasBoundedOpenStabilizers`: KP Axiom 4.1.2, for the topology
   `rationalPointTopology F G.X`;
3. `P.SatisfiesAffineApartmentAxiom T`: KP Axiom 4.1.4 (A 0–A 2) for the
   derived subgroup, its maximal split torus `S'` and the split component
   `A_G` supplied by `T`;
4. `P.HasRootReflections`: AS 1 of KP Axiom 4.1.6, `m(u)` fixes `H_u`;
5. `P.HasCompatibleApartmentFacets`: AS 6 of KP Axiom 4.1.6, with
   injectivity of the apartment map;
6. `P.HasTitsSystem`: the corrected KP Axiom 4.1.9 for every chamber of
   `A(S)`.

With the premise, these are the seven Library predicates of the corrected
opening of KP Section 4.2, used as premises by
`BoundedSubgroupFixedPointStatement`, `MetricRealizationStatement` and
`ApartmentConjugacyFixingIntersectionStatement`, and asserted by
`RootValuationBuildingConstructionStatement`.

## Source correspondence

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

- The standing hypotheses of Chapter 7 are at its opening, printed p.235 /
  PDF p.266: `k` is Henselian with a discrete valuation (the residue field need
  not be perfect), `G` is connected reductive, Axiom 4.1.4 holds, and each
  `A(S)` is an equipollence class of valuations of the root datum of `(G, S)`
  with the action of `N(k)` of §6.1.8.
- KP 4.1.28, printed p.166 / PDF p.197, lists where the axioms are proved for
  the Chapter 7 building: AS 1 is Proposition 6.2.1 and AS 6 holds by the
  construction of `B(G)`; Theorem 7.5.3 constructs the Iwahori–Tits system and
  verifies the first part of Axiom 4.1.9; Definition 7.6.1 establishes Axiom
  4.1.1 except the bijection between maximal split tori and apartments, which
  is Proposition 7.6.3; Corollary 7.3.14 and Propositions 7.6.4, 7.7.1 and
  7.7.5 establish Axiom 4.1.2 and the second part of Axiom 4.1.9.
- Remark 7.6.5, printed p.266 / PDF p.297: Proposition 7.6.4 "completes the
  proof of Axioms 4.1.1, 4.1.4, and 4.1.9", and the building is realized as the
  quotient (7.6.2) of `G(k) × A`. Proposition 7.6.8 and Corollary 7.6.9, on the
  same page, give the stabilizer `N(k)` of `A` and the equivariant bijection
  between maximal split tori and apartments.
- Proposition 7.6.3 is on printed p.264 / PDF p.295, Proposition 7.6.4 on
  printed p.265 / PDF p.296, and Propositions 7.7.1 and 7.7.5 on printed
  pp.267–270 / PDF pp.298–301.

The authors' corrections of 1 November 2024,
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`:

- PDF p.33: at the end of the second paragraph of Chapter 7 the authors add
  that AS 1–AS 4 are proved in §6.3 and that "We will assume in addition that
  assertion AS 5 holds"; PDF p.35 uses AS 5 in the proof of Theorem 7.5.1.
- PDF pp.27–28: the corrected axiom list of Definition 4.1.26, and Axiom
  4.1.6 added to the hypotheses of Section 4.2.

## Derived scope and provenance

This is a derived formulation, not a literal transcription.

- **Field.** The statement covers nonarchimedean local fields, of mixed and
  equal characteristic. Other fields allowed by KP Chapter 7 are not covered.
- **The building.** KP Chapter 7 defines `B(G)` as the restricted building
  of the Iwahori–Tits system (Definition 7.6.1) and realizes it as the
  quotient (7.6.2) (Remark 7.6.5). Here the building is the Library's quotient
  `P.toValuationBuildingData.ReducedBuilding`, with its existing action of
  `G(F)`; the polysimplicial structure `R` and the splitting `T` are asserted
  to exist.
- **Hypotheses.** The premise is the Library predicate
  `SatisfiesApartmentAxioms`. It contains AS 5, which the corrected Chapter 7
  assumes, and AS 2–AS 4, which KP prove in §6.3 for every valuation. It
  also contains V 7, which is not among the standing hypotheses of Chapter 7;
  the statement is weaker than KP's by this extra premise. V 6 is part of the
  data `P`. The premise matches the Chapter 7 statements
  `AffineIwahoriTitsStatement`, `RootGroupActionAxiomStatement` and
  `IwahoriDecompositionAxiomStatement`.
- **Axiom 4.1.1.** Only the clauses for `G` alone are asserted. The
  comparisons between groups are the separate statement
  `BuildingComparisonAxiomStatement`.

No existence of the data is asserted. With this statement,
`RootValuationBuildingConstructionStatement` reduces to the existence of
`P : ParahoricBuildingData G` with `P.SatisfiesApartmentAxioms` for every
connected reductive `G`, which is the content of KP Theorem 9.6.5 and
Proposition 9.4.35. The statement also applies to the restricted data of a
Levi subgroup once those data satisfy `SatisfiesApartmentAxioms`.

## Expected proof route (not prescribed)

Much of this is already assembled conditionally in the Library:
`TitsBuildingAxiomAssembly`, `AffineTitsRealizationBuilding` and
`BaseApartmentRealizationBuilding` (Axiom 4.1.1 for the restricted Tits
realization), `BoundedOpenStabilizerAssembly` (Axiom 4.1.2),
`ValuationBuildingTitsSystemTransport`, the Chapter 7 inputs of
`AffineIwahoriTitsInputStatements` and `AffineIwahoriTitsStatement` (Theorem
7.5.3), and `AnisotropicFiveAxiomConstruction` (the anisotropic case). The
remaining inputs include Theorem 7.5.3 itself, AS 1 (Proposition 6.2.1), and
the existence of the splitting `T` from the derived subgroup and the split
component of `G`.
