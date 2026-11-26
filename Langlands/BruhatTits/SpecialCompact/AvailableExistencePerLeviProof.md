# Existence of a special maximal compact subgroup for available Bruhat–Tits data, with an assignment for each standard Levi: proof

The theorem
`Langlands.BruhatTits.SpecialCompact.availableSpecialMaximalCompactExistencePerLevi` proves
exactly `AvailableSpecialMaximalCompactExistencePerLevi.{u}` (module
`Langlands.BruhatTits.SpecialCompact.AvailableExistencePerLeviStatement`) for an arbitrary
universe `u`. It has no hypothesis.

## What is proved

For every nonarchimedean local field `F : Type u` (mixed or equal characteristic), every
connected reductive `G` over `F`, every maximal split torus `i : S → G` and every generic
cocharacter `ν` of `S`, there are an assignment `𝔅` and apartment data `D` for `(G, S)` such
that:

- Bruhat–Tits theory is available for `G` in `𝔅` (corrected KP Definition 4.1.26, as
  `KPBuildingAssignment.IsAvailableFor`), and the data of `𝔅` for `G` have the torus
  `i : S → G` and the apartment `D`;
- some special vertex `x` of the apartment has compact stabilizer
  `K_0 = D.specialCompactSubgroup x = G(F)^1 ∩ G(F)_x` with the properties
  `SpecialCompactProperties F i ν K_0`: open, bounded and compact, maximal among bounded and
  among compact subgroups, containing representatives of the relative Weyl group, and
  satisfying `K_0 ∩ P_J = (K_0 ∩ M_J)(K_0 ∩ U_J)` for every standard parabolic `P_J`;
- for every set `J` of simple relative roots, the actual standard Levi `M_J` is connected
  reductive, and some assignment `𝔅M` is available for `M_J`, with data based at the torus
  `S → M_J` and an apartment `DM` containing a point `xM` related to `x` by
  `SpecialLeviRestriction`.

The statement's Markdown page gives the precise reading of each clause.

## Proof

The proof is a composition of published theorems; it is one term.

1. **The one-group clauses of corrected Definition 4.1.26.**
   `groupAxiomsExistenceReduction` (module
   `Langlands.Geometry.Building.GroupAxiomsExistenceReduction`) proves
   `GroupAxiomsExistenceReductionStatement`: the four focused statements below imply
   `GroupAxiomsExistenceStatement`, which says that every connected reductive group over every
   nonarchimedean local field in universe `u` carries a `KPBuildingDatum` satisfying every
   clause of the ten corrected axioms that concerns the group alone. The proof applies it to
   the four Library theorems
   - `rootValuationBuildingConstruction` (module
     `Langlands.Geometry.Building.RootValuationBuildingConstructionProof`), proving
     `RootValuationBuildingConstructionStatement`: root-valuation building data with a
     polysimplicial realization and an apartment splitting satisfying Axioms 4.1.1 (for `G`
     alone), 4.1.2, 4.1.4, 4.1.6 and 4.1.9;
   - `rootGroupActionAxiom` (module `Langlands.Geometry.Building.RootGroupActionAxiomProof`),
     proving `RootGroupActionAxiomStatement`: Axiom 4.1.8 (2) and (3) on supplied data;
   - `iwahoriDecompositionAxiom` (module
     `Langlands.Geometry.Building.IwahoriDecompositionAxiomProof`), proving
     `IwahoriDecompositionAxiomStatement`: Axiom 4.1.16 on supplied data;
   - `integralModelAxioms` (module `Langlands.Geometry.Building.IntegralModelAxiomsProof`),
     proving `IntegralModelAxiomsStatement`: Axioms 4.1.20 and 4.1.22 on supplied data.

2. **Availability.** `bruhatTitsAvailabilityReduction` (module
   `Langlands.Geometry.Building.BruhatTitsAvailabilityReductionProof`) proves
   `GroupAxiomsExistenceStatement.{u} → BruhatTitsAvailabilityStatement.{u}`. Applied to the
   term of step 1, it gives `BruhatTitsAvailabilityStatement.{u}`: some
   `KPBuildingAssignment.{u}` is valid, that is, satisfies all ten corrected axioms including
   the comparisons between groups and fields of Axioms 4.1.1 and 4.1.17 (the Definition 4.1.26
   conclusion of KP Theorem 9.2.7, for nonarchimedean local fields).

3. **The target.**
   `availableSpecialMaximalCompactExistencePerLevi_of_bruhatTitsAvailability` (module
   `Langlands.BruhatTits.SpecialCompact.AvailableExistencePerLeviReduction`) proves
   `BruhatTitsAvailabilityStatement.{u} → AvailableSpecialMaximalCompactExistencePerLevi.{u}`.
   Applied to the term of step 2, it gives the target. Its own proof rebases the valid
   assignment at `(G, i)`, takes a special vertex of the based apartment with the special
   compact properties, and for each standard Levi rebases the valid assignment at
   `(M_J, S → M_J)` and finds the restricted special vertex; its Markdown page describes this.

All universe levels are the same `u` throughout. The theorem uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

The statement formalizes KP Theorem 4.2.15(1) at a special vertex and Renard, Théorème
V.5.1(2), (3), (5), for available data with an assignment for each standard Levi; its
Markdown page gives the source comparison:

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
  `kaletha-prasad-2023-bruhat-tits-new-approach`: Definition 4.1.26, Theorem 4.2.15(1),
  Theorem 9.2.7;
- Kaletha–Prasad, corrections of 1 November 2024, `kaletha-prasad-2024-corrections`: the
  corrected Definition 4.1.26;
- Renard, *Représentations des groupes réductifs p-adiques*,
  `renard-2026-representations-groupes-reductifs-padiques`: Théorème V.5.1 (printed page 122,
  PDF page 128).

This proof is an internal composition of published Library theorems. As in KP, existence of
the special compact subgroup is derived from the availability of Bruhat–Tits theory (KP
Theorem 9.2.7), but availability is obtained here through the Library's reductions of
Definition 4.1.26 to the focused statements above, not by the argument of KP §9.5.
