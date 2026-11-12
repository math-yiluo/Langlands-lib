# Integral models with Axioms 4.1.20 and 4.1.22 on supplied building data

`Langlands.Geometry.Building.IntegralModelAxiomsStatement` is a Prop-valued
`def` at every universe `u`. It asserts that supplied building data satisfying
the five axioms of the corrected opening of Kaletha–Prasad Section 4.2 carry
integral models satisfying Axioms 4.1.20 and 4.1.22. The module supplies no
proof.

## Statement

The proposition quantifies over:

- every nonarchimedean local field `F`, of either characteristic;
- every group scheme `G` over `Spec F` with `[IsAffineHom G.X.hom]`;
- every `P : ParahoricBuildingData G`, polysimplicial structure
  `R : P.toValuationBuildingData.PolysimplicialRealization` and splitting
  `T : P.toValuationBuildingData.ApartmentSplitting`. The data `P` consist of
  a maximal split torus `S`, the class `A(S)` of valuations of the root datum
  normalized by the valuation of `F`, the actual centralizer with V 6, and the
  data for `Z(F)^0` and `G(F)^0`. Connected reductivity of `G` is a field of
  the data.

It assumes the seven Library predicates for the axioms of the corrected
opening of KP Section 4.2, with Axiom 4.1.1 restricted to its clauses for `G`
alone: `P.SatisfiesBuildingAxiom R` (4.1.1 for `G`),
`P.HasBoundedOpenStabilizers` (4.1.2), `P.SatisfiesAffineApartmentAxiom T`
(4.1.4), and `P.HasRootReflections`, `P.SatisfiesApartmentAxioms` (V 7 and
AS 2–AS 5) and `P.HasCompatibleApartmentFacets` (together AS 1–AS 6 of 4.1.6),
and `P.HasTitsSystem` (4.1.9). These are the premises of the published
`BoundedSubgroupFixedPointStatement` and `MetricRealizationStatement`, and the
conclusion of `RootValuationBuildingConstructionStatement`.

The conclusion asserts the existence of:

- `M : BuildingModelFamily P.toValuationBuildingData 𝒪[F]` (module
  `Langlands.BruhatTits.IntegralModels.ModelFamily`): for every non-empty
  bounded subset of an apartment `g · A(S)` and every facet of `B(G)`, a
  smooth affine model `G¹_Ω` over the valuation ring `𝒪[F]` with generic
  fibre `G`, its relative identity component `G⁰_Ω` with connected fibres, the
  generic-identity morphisms `G¹_{Ω′} → G¹_Ω` for `Ω ≺ Ω′` and for incident
  facets, and an integral torus for every chart presentation;
- `Q : BuildingModelQuotientFamily P.toValuationBuildingData M` (module
  `Langlands.BruhatTits.IntegralModels.FacetAxioms`): for every facet `F` of
  `B(G)`, a unipotent radical and quotient of the special fibre of `G⁰_F`;
- `ρ : RelativeRootReflectionData P.i`: coroots and reflection representatives
  of the relative roots of `S`;

such that `M.SatisfiesModelAxioms P` and `Q.SatisfiesMorphismAxioms ρ`.

- `M.SatisfiesModelAxioms P` (Axiom 4.1.20) is `ModelAxiomClauses`: the
  integral points of `G¹_Ω` are the norm-one pointwise fixer `G(F)^1_Ω` and
  those of `G⁰_Ω` are the zero fixer `G(F)^0_Ω`; (1) a non-empty subset of a
  facet has the neutral model of the facet; (2) closure does not change the
  neutral model; (3) the integral tori are closed split tori whose special
  fibres are maximal split; (4) `G⁰_Ω = G¹_Ω` when `G` is simply connected.
- `Q.SatisfiesMorphismAxioms ρ` (Axiom 4.1.22) is the conjunction of
  `M.SatisfiesGeneralMorphismAxioms` (the preamble and part (1): the special
  fibre maps restrict to tori isomorphically and have smooth connected
  unipotent kernels) and `Q.SatisfiesFacetAxioms ρ`: the quotients are the
  maximal reductive quotients, and parts (2)–(7) for incident facets
  `F ≺ F′` (parabolic images, common maximal split tori and the sign rule for
  Lie weights, reduction preimages, the order bijection onto parabolic
  subgroups, the root datum of the reductive quotient from the affine roots
  vanishing on the facet, and the positive radicals).

These are exactly the fields `bruhatTitsGroupSchemes` and
`reductiveQuotients` of `KPBuildingDatum.SatisfiesGroupAxioms` for the datum
`⟨P, R, T, M, Q, ρ⟩`.

## Source correspondence

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

- Axiom 4.1.20, printed p.163 / PDF p.194: "Given a non-empty bounded subset
  `Ω` of an apartment `A` of `B(G)`, there is a smooth affine `o`-group scheme
  `G¹_Ω`, with generic fiber `G`, such that `G¹_Ω(o) = G(k)¹_Ω`. Letting
  `G⁰_Ω` be the relative identity component of `G¹_Ω` we have
  `G⁰_Ω(o) = G(k)⁰_Ω`", with properties (1)–(4).
- Axiom 4.1.22, printed pp.163–164 / PDF pp.194–195: for `Ω ≺ Ω′` a
  homomorphism `ρ_{Ω′,Ω} : G¹_{Ω′} → G¹_Ω` that is the identity on the generic
  fibre, with properties (1)–(7), (2)–(7) for facets `F ≺ F′`.
- KP 4.1.28, printed p.166 / PDF p.197: for quasi-split groups Axiom 4.1.20
  is proved mostly in Chapter 8 (Theorems 8.3.2 and 8.3.13, Propositions 8.2.2
  and 8.2.4, Corollary 2.10.11), and Axiom 4.1.22 in §8.4 (Proposition 8.4.15,
  Theorems 8.4.10 and 8.4.19, Corollary 8.4.12).
- §9.5, printed pp.363–364 / PDF pp.394–395: for general `G` the group schemes
  of Axiom 4.1.20 are those of 9.2.5, with `G¹_Ω(o) = G(k)¹_Ω` and
  `G⁰_Ω(o) = G(k)⁰_Ω` from Proposition 9.3.24, and the parts of Axiom 4.1.22
  descend from the quasi-split group over the maximal unramified extension,
  using perfectness of the residue field for (7), Proposition 9.3.3 for (4)
  and Proposition 9.4.23 for (6).
- Uniqueness: Proposition 4.4.6 and Corollary 4.4.7, printed pp.184–185 / PDF
  pp.215–216, show that a building satisfying Axioms 4.1.1, 4.1.4, 4.1.8 and
  4.1.9 is determined as a `G(k)`-set by its apartment.

The authors' corrections of 1 November 2024,
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`:

- PDF p.27 keeps Axioms 4.1.20 and 4.1.22 in the corrected list of Definition
  4.1.26 and adds 4.1.6 to the hypotheses of Section 4.2.
- PDF pp.37–38 correct the hypotheses and morphism setup of Theorem 8.4.19.
  As recorded in the KP source ledger (section "Bundle D"), the smaller index
  set printed in Theorem 8.4.19 (1) is not used: the kernel clause here is
  part (1) of Axiom 4.1.22, smooth connected unipotent.

## Derived scope and provenance

This is a derived formulation, not a literal transcription.

- **Supplied data.** KP prove the axioms for the models of their own
  construction. Here the models are asserted to exist for any supplied data
  satisfying the five Section 4.2 axioms on the Library's valuation quotient.
  This is expected to hold because such data determine the building:
  the apartment class is unique by Proposition 6.2.6 (proved in the Library
  as `omegaCompatibleApartmentUniqueness`), and the axioms make the quotient
  KP's building (Proposition 4.4.6, Corollary 4.4.7). Axioms 4.1.8 and 4.1.16
  are not premises; for the Library's valuation quotients KP derive them from
  the Chapter 7 hypotheses, which are contained in `P.SatisfiesApartmentAxioms`.
- **Field and base.** The statement covers nonarchimedean local fields of
  either characteristic. Their residue fields are finite, hence perfect, as
  §9.5 requires. The models are over the valuation ring `𝒪[F]`.
- **Formalized axioms.** The conclusion uses the published predicates for
  Axioms 4.1.20 and 4.1.22 without change.

No existence of `P`, `R`, `T` or of the premises is asserted. Together with
`RootValuationBuildingConstructionStatement`, `RootGroupActionAxiomStatement`
and `IwahoriDecompositionAxiomStatement`, this statement implies
`GroupAxiomsExistenceStatement`: take `P`, `R` and `T` from the first and
assemble the datum `⟨P, R, T, M, Q, ρ⟩`; Axiom 4.1.8 (1) is
`ValuationBuildingData.hasHalfApartmentFixers`.

## Expected proof route (not prescribed)

KP construct the models over the ring of integers `O` of the maximal
unramified extension `K` for the quasi-split group `G_K` (Chapter 8:
schematic root data, Theorems 8.3.2 and 8.3.13, §8.4), then descend them to
`o` by invariant coordinate rings and relative identity components (§9.2.5),
and verify the axioms over `o` in §9.5. Comparing the descended building with
`P` uses the every-point comparison of §9.6.6 and corrected Corollary 4.4.5,
as in the route of `RootValuationBuildingConstructionStatement`. Library
interfaces for the descent include `MaximalUnramified.BuildingData`,
`UnramifiedStabilizerDescent` and `Langlands.GroupScheme.IntegralModel`.
