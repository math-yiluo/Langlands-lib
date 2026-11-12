# Data satisfying the one-group clauses of corrected Definition 4.1.26 exist

`Langlands.Geometry.Building.GroupAxiomsExistenceStatement` is a Prop-valued
`def` at every universe `u`. It asserts that every connected reductive group
over a nonarchimedean local field has building and integral-model data
satisfying every clause of the ten axioms of corrected Kaletha–Prasad
Definition 4.1.26 that concerns the group alone. The module supplies no
proof.

## Statement

The proposition quantifies over every nonarchimedean local field `F`, of
either characteristic, and every group scheme `G` over `Spec F` with
`[IsAffineHom G.X.hom]` and `IsConnectedReductive G`. It asserts
`∃ D : KPBuildingDatum G, D.SatisfiesGroupAxioms`.

`KPBuildingDatum G` (module
`Langlands.Geometry.Building.FullValidity.Assignment`) consists of:

- `base : ParahoricBuildingData G`: the reduced building `B(G)` (the quotient
  of `G(F) × A(S)`), a maximal split torus `S`, the class `A(S)` of
  valuations of the root datum, the actual centralizer with V 6, and the data
  for `Z(F)^0` and `G(F)^0`;
- `realization`: a polysimplicial structure on `B(G)`;
- `splitting`: the tori of Axiom 4.1.4;
- `models`: integral models over `𝒪[F]` for the non-empty bounded subsets of
  apartments and for the facets, with their morphisms and integral split tori;
- `quotients`: unipotent radicals and reductive quotients of the special
  fibres of the facet models;
- `rootDatum`: coroots and reflection representatives of the relative roots.

`D.SatisfiesGroupAxioms` is the structure with the nine fields `building`
(Axiom 4.1.1 for `G` alone), `boundedSubgroups` (4.1.2), `affineStructure`
(4.1.4), `affineRootSystem` (4.1.6, AS 1–AS 6 with V 7), `rootGroupAction`
(4.1.8), `titsSystem` (4.1.9), `iwahoriDecomposition` (4.1.16),
`bruhatTitsGroupSchemes` (4.1.20) and `reductiveQuotients` (4.1.22). It
omits the comparisons between groups in Axiom 4.1.1 and Axiom 4.1.17.

## Source correspondence

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

- Theorem 9.2.7, printed p.329 / PDF p.360: for a connected reductive group
  `G` over a discretely valued field `k` with Henselian valuation ring and
  perfect residue field, the descended building `B(G_K)^Γ` with its
  apartments, polysimplicial structure and the group schemes of 9.2.5
  satisfies Axioms 4.1.1, 4.1.4, 4.1.6, 4.1.9, 4.1.17, 4.1.20 and 4.1.22, and
  Bruhat–Tits theory is available for `G`.
- §9.5, printed pp.363–364 / PDF pp.394–395, assembles the proofs of the
  axioms, including 4.1.2 and 4.1.8 (Proposition 9.4.3, Lemmas 9.4.6 and
  9.4.21).
- KP 4.1.28, printed p.166 / PDF p.197, lists where each axiom is proved for
  quasi-split groups (Chapters 6–8), including 4.1.16 (Corollary 7.4.9) and
  4.1.20, 4.1.22 (Chapter 8).

The authors' corrections of 1 November 2024,
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, PDF
p.27, replace the axiom list of Definition 4.1.26 by Axioms 4.1.1, 4.1.2,
4.1.4, 4.1.6, 4.1.8, 4.1.9, 4.1.16, 4.1.17, 4.1.20 and 4.1.22.

## Derived scope and provenance

This is a derived formulation, not a literal transcription.

- **Clauses for one group.** The statement asserts the one-group clauses of
  all ten corrected axioms, which is more than the seven axioms listed in
  Theorem 9.2.7 and fewer than full availability. The source routes for
  4.1.2, 4.1.8 and 4.1.16 for the descended building are recorded in the
  certificate map of the KP source ledger
  (`notes/bruhat-tits/kp-source-ledger.md`).
- **Existence, not a construction.** KP prove the axioms for their
  construction `B(G_K)^Γ`. The statement only asserts that some data satisfy
  them. Axiom 4.1.27 (unramified descent) is not part of it.
- **Field.** The statement covers nonarchimedean local fields of either
  characteristic. Their residue fields are finite, hence perfect, and their
  valuation rings are Henselian.

The published `RootValuationBuildingConstructionStatement` asks for the five
axioms of KP Section 4.2 on parahoric building data; this statement asks for
all one-group clauses on a full `KPBuildingDatum`. Together with
`BuildingComparisonAxiomStatement` (the comparisons of Axiom 4.1.1 for all
data) and `IsomorphismCompatibilityAxiomStatement` (Axiom 4.1.17 for all
data), it implies `BruhatTitsAvailabilityStatement`: choose a datum for every
group and apply `KPBuildingAssignment.isAvailableFor_iff`.

## Expected proof route (not prescribed)

Take `P`, the realization and the splitting from a proof of
`RootValuationBuildingConstructionStatement`, which supplies Axioms 4.1.1 for
`G` alone, 4.1.2, 4.1.4, 4.1.6 and 4.1.9. For the same `P`, Axioms 4.1.8 and
4.1.16 follow from KP Chapter 7 (Proposition 7.7.5, Lemma 7.7.3 and
Corollary 7.4.9), whose hypotheses are contained in `P.SatisfiesApartmentAxioms`;
the statements `RootGroupActionAxiomStatement` and
`IwahoriDecompositionAxiomStatement` record these steps. Axiom 4.1.8 (1) is
already proved for all data (`ValuationBuildingData.hasHalfApartmentFixers`).
The integral models, special-fibre quotients and relative root data of Axioms
4.1.20 and 4.1.22 come from KP Chapter 8 and §9.2.5 and remain to be
constructed for that `P`.
