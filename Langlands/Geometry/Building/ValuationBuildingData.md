# Building data for an `ω`-compatible valuation of the root datum

This module belongs to the task on actual Kaletha–Prasad affine-root,
special-point, parahoric and compact-stabilizer objects. It is the adapter of
the task's objective 4. The structure `ValuationBuildingData G` collects, for
an actual connected reductive group `G` over a nonarchimedean local field `F`,
the data that KP Chapter 7 assumes before constructing the building, except
the assumption AS 5 added by the corrections (see below). Under one
namespace it then exposes the objects of the modules `KPApartment`,
`KPBuilding`, `KPRootFixerPlus` and `KPCentralizerCompatibility` built from
those data. These are the rational-point action, the actual root groups and
their filtrations, the affine roots, facets, chambers, vertices, special
points, fixers and `K_y`.

The module adds no new mathematics. The structure is a bundle of existing
data and predicates. Each other declaration is an abbreviation for an existing
definition or a one-line restatement of a law proved in those modules. The
exceptions are the predicates `IsFacet`, `IsChamber` and `IsVertex` on the
building, and the lemma `mono_of_isMaximalSplitTorus`.

Two later modules of the same task build on this one. `KPParahoric` defines
`ParahoricBuildingData G`, which extends `ValuationBuildingData G` by the
data of `Z(F)^0` and `G(F)^0` (module `KPZeroSubgroups`) and defines the
parahoric subgroups. Worker 1045's `ValuationBuildingAxioms` states, as
conditions on `B : ValuationBuildingData G`, the clauses of KP's axioms that
are not fields here, among them V 7 and AS 2–AS 5. This Markdown describes
only this module; the two later modules are cited where they fill a gap
listed below.

## Sources

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`:

- Chapter 7, opening paragraphs, printed pp. 235–236, PDF pp. 266–267: the
  standing data of the chapter. These are a connected reductive `G` and a
  maximal split torus `S`. The affine space `A(S)` is an equipollence class of
  valuations of the root datum of `(G, S)` (Definitions 6.1.2 and 6.1.7). It
  carries the `N(k)`-action of §6.1.8 and satisfies Axiom 4.1.4, with
  `ω(k^×) = ℤ`.
- Definition 6.1.2, printed p. 199, PDF p. 230: valuations of the root datum,
  the filtrations `U_{a,x,r}` and `U_{a,x,r+} = ⋃_{s>r} U_{a,x,s}` (last
  paragraph), and the axiom V 6, which defines `ω`-compatibility.
- Definition 6.1.7 and §6.1.8, printed p. 201, PDF p. 232: equipollence
  classes and the action of `N(k)`.
- Axiom 4.1.4 (A 1), printed pp. 158–159, PDF pp. 189–190: `Z(k)` acts on
  `A(S)` by translation by `ν(z) = -ω_Z(z)`.
- Definitions 6.3.1 and 6.3.4, printed pp. 217–218, PDF pp. 248–249: the
  affine root groups `U_ψ` and the affine roots `Ψ`.
- Definition 1.3.39, printed p. 29, PDF p. 60: special points.
- Definition 7.4.1(1) and (2), printed p. 255, PDF p. 286: `U_{a,Ω,0}` and
  `G(k)^♯_Ω`.
- Proposition 7.6.3 and Remark 7.6.5, printed pp. 264–266, PDF pp. 295–297:
  the building as the quotient (7.6.2) of `G(k) × A`. The apartment `A`, with
  the polysimplicial structure given by the affine-root hyperplanes, realizes
  the standard apartment of `B(G)`.
- Notation 2.6.15 and Lemma 2.6.16, printed pp. 102–103, PDF pp. 133–134, and
  Theorem 4.2.15, printed p. 173, PDF p. 204: `G(k)^1` and the stabilizers
  `G(k)^1_x`.

The corrections of 1 November 2024 (`kaletha-prasad-2024-corrections`) were
checked. Three of them matter here.

- PDF p. 25 removes the minus sign of `ω_G` in §2.6(d). The translation
  `ν = -ω_Z` of `KPCentralizerCompatibility` uses the corrected sign.
- PDF p. 33 adds sentences at the end of the second paragraph of Chapter 7.
  The action of `N(k)` on `A(S)` gives a map from `N(k)` to the extended
  affine Weyl group `W(Ψ)_ext` whose image contains `W(Ψ)`. Assertions
  AS 1–AS 4 of Axiom 4.1.6 are proved in §6.3. KP then assume in addition
  that AS 5 holds. This assumption is not a field of the structure here; see
  the section on the structure below.
- PDF p. 27 replaces the axiom list of Definition 4.1.26. The corrected list
  is Axioms 4.1.1, 4.1.2, 4.1.4, 4.1.6, 4.1.8, 4.1.9, 4.1.16, 4.1.17, 4.1.20
  and 4.1.22.

The corrections do not change Definitions 6.1.2, 6.1.7, 6.3.1, 6.3.4 and
7.4.1, §6.1.8, the relation (7.6.2) or Theorem 4.2.15.

## Inputs

- The field. `F` is a nonarchimedean local field, `[Field F] [ValuativeRel F]
  [TopologicalSpace F] [IsNonarchimedeanLocalField F]`. Its topology enters
  only through these instances. KP's `ω` is `localFieldOrder F` of
  `KPBuilding`, the normalized order with `ω(F^×) = ℤ`.
- The group. `G : GroupScheme (Spec (CommRingCat.of F))` with
  `[IsAffineHom G.X.hom]`. `G(F)` is `rationalPoints G`.
- The torus. `S` is a commutative group scheme over `F` with `i : S.toGrp ⟶ G`
  satisfying the published `IsMaximalSplitTorus i`.
- The roots are the published `relativeRoots i`. The root groups are the
  `F`-points of the published `RelativeRoot.subgroup i a`.
- The centralizer is `CentralizerDatum i` of `KPCentralizerCompatibility`. It
  consists of a group scheme `Z`, a closed subgroup `j : Z ⟶ G` representing
  the actual torus centralizer, `s : S.toGrp ⟶ Z` with `s ≫ j = i`, and
  bijectivity of the character comparison `Cartan.restrictionEvaluation s`.

## The structure

`ValuationBuildingData G : Type (u + 1)` has the fields

- `isConnectedReductive : IsConnectedReductive G`;
- `S`, `i` and `isMaximalSplitTorus : IsMaximalSplitTorus i`;
- `apartment : KPApartmentData i (localFieldOrder F)`, an `N(F)`-stable
  equipollence class of valuations of the root datum of `(G, S)` normalized by
  `ω` (Definitions 6.1.2, 6.1.7, §6.1.8);
- `centralizer : CentralizerDatum i`;
- `isOmegaCompatible : apartment.IsOmegaCompatible centralizer`, the axiom
  V 6 of Definition 6.1.2 for every valuation of the class and all of `Z(F)`.

`KPApartmentData` needs `Mono i.hom.hom.left`. The lemma
`mono_of_isMaximalSplitTorus` derives it: a maximal split torus is a closed
immersion (`IsSplitSubtorus`), hence a monomorphism. The structure uses it
through `haveI` in the types of its fields, and `ValuationBuildingData`
installs it as an instance for `B.i`.

These fields are the standing data of KP Chapter 7, with two differences.

- KP assume an affine space `A(S)` for every maximal split torus, with
  isomorphisms `A(S) → A(gSg⁻¹)` for `g ∈ G(k)`. Here there is one torus `S`,
  as in KP's construction of the building from `A = A(S)` by (7.6.2). The
  apartments `g · A(S)` of the building are `G(F)`-translates of the image of
  `A(S)`.
- The corrected opening of Chapter 7 also assumes AS 5 of Axiom 4.1.6 for
  the affine root system `Ψ`. AS 5 is about the image of `N(k)` in the
  extended affine Weyl group. It is not a field here, and nothing in this
  module uses it. The later module `ValuationBuildingAxioms` states it on top
  of `ValuationBuildingData`: the condition `B.SatisfiesApartmentAxioms`
  includes AS 5, written with `B.affineRoots` and the published
  `AffineRootSystem.affineWeylGroup` and
  `AffineRootSystem.extendedAffineWeylGroup` (module `AffineWeylGroups`).

KP's Axiom 4.1.4 (A 1) says, among other things, that `z ∈ Z(k)` acts on
`A(S)` by translation by `ν(z)`. For valuations with the action of §6.1.8,
`(z · φ)_a(u) = φ_a(z⁻¹ u z)`, so `z · φ = φ + ν(z)` is exactly V 6 for `z`.
KP prove the direction from V 6 in Propositions 6.2.3 and 6.2.4, and
`KPCentralizerCompatibility` proves it in Lean
(`IsCentralizerCompatible.smul_eq_vadd`).
`isConnectedReductive` is not used in the proofs. It records KP's hypothesis
on `G`.

## The exposed names

For `B : ValuationBuildingData G`:

- `B.Apartment` is `A(S)`, an affine space over `TranslationSpace B.i`, the
  quotient of `V(S)` by the annihilator of the roots.
- `B.ReducedBuilding` is the reduced building `B(G)` of Remark 7.6.5, the
  quotient (7.6.2) of `G(F) × A(S)` built in `KPBuilding` with `G(F)^♯_x`. It
  carries the `G(F)`-action `g • [h, x] = [gh, x]`.
- `B.apartmentMap : B.Apartment → B.ReducedBuilding` is `x ↦ [1, x]`.
  `exists_smul_apartmentMap`: every point of the building is `g • [1, x]`.
  `normalizer_smul_apartmentMap`: for `n ∈ N(F)`,
  `n • [1, x] = [1, n · x]`, with the action of §6.1.8 on `A(S)`.
- `B.rootGroup a` is `U_a(F)`, the `F`-points of the actual relative root
  subgroup functor (`rootGroup_eq`). `B.doubleRootGroup a` is `U_{2a}(F)`,
  trivial if `2a` is not a root.
- `B.filtration x a r` is `U_{a,x,r} = {u ∈ U_a(F) | x_a(u) ≥ r}`
  (Definition 6.1.2, V 1). If `a` is not a root it is `U_a(F)`.
  `filtration_le_rootGroup` holds. `B.filtrationPlus x a r` is
  `U_{a,x,r+} = ⋃_{s>r} U_{a,x,s}` (Definition 6.1.2, last paragraph).
- `B.affineRootGroup a ψ` is `U_ψ` (Definition 6.3.1), and `B.affineRoots` is
  the set `Ψ` of affine roots (Definition 6.3.4) of `KPApartment`.
- `B.IsSpecialPoint y` means that `y = g • [1, x]` with `x` special for `Ψ` in
  the sense of Definition 1.3.39. This is `KPBuilding`'s
  `IsSpecialBuildingPoint`.
- `B.IsFacet Y`, `B.IsChamber Y` and `B.IsVertex y` say that `Y`
  (respectively `y`) is the `G(F)`-translate of the image in `B(G)` of a facet
  (respectively chamber, vertex) of `A(S)` for `Ψ`. Facets, chambers and
  vertices of `A(S)` are those of the published `AffineRootSystem`.
  `isFacet_image`, `isChamber_image` and `isVertex_apartmentMap` show that
  images of facets, chambers and vertices of `A(S)` qualify. `IsFacet.smul`,
  `IsChamber.smul` and `IsVertex.smul` show that the three predicates are
  `G(F)`-stable.
- For `Ω ⊆ A(S)`, `B.rootFixer a Ω` is
  `U_{a,Ω,0} = U_a(F) ∩ ⋂_{x ∈ Ω} U_{a,x,0}` (Definition 7.4.1(1)), and
  `B.rootFixerPlus a Ω` is `U_{a,Ω,0+} = U_a(F) ∩ ⋂_{x ∈ Ω} U_{a,x,0+}`.
  The second is `KPRootFixerPlus`'s positive-depth analogue of
  Definition 7.4.1(1); KP use it for facets in 6.3.21 and Corollary 7.4.9.
  Intersecting with `U_a(F)` makes both equal to `U_a(F)` for empty `Ω`.
  `rootFixerPlus_le_rootFixer` holds.
- `B.fixer y` is the stabilizer `G(F)_y` of `y`, `B.pointwiseFixer Y` is the
  pointwise fixer of `Y`, `B.sharpFixer Ω` is `G(F)^♯_Ω` (Definition 7.4.1(2))
  for `Ω ⊆ A(S)`, and `B.compactStabilizer y` is
  `K_y = G(F)^1 ∩ G(F)_y` (Theorem 4.2.15), with `G(F)^1` the published
  `Plancherel.rationalCommonNormKernel G`. `mem_fixer`,
  `mem_compactStabilizer`, `compactStabilizer_le_fixer` and
  `sharpFixer_le_fixer` (`G(F)^♯_x ⊆ G(F)_{[1, x]}`) hold.
- `B.translation` is `ν : Z(F) → V(S)`, `ν(z) = -ω_Z(z)` (Axiom 4.1.4 (A 1)).
  `centralizer_smul_apartmentMap`: `j(z) • [1, x] = [1, x + [ν(z)]]`, where
  `[ν(z)]` is the class of `ν(z)` in `TranslationSpace B.i`.
  `map_mem_compactStabilizer`: `j(z) ∈ K_{[1, x]}` for `z ∈ Z(F)^1` and
  `x ∈ A(S)`.

### Provenance of the building facets

KP define the polysimplicial structure of `B(G)` through the Iwahori–Tits
system of §7.5 and Proposition 1.5.18. By Proposition 7.6.3(1), `A(S)` with the
structure given by the affine-root hyperplanes realizes the standard
apartment. Since the action of `G(k)` preserves the polysimplicial structure
(proof of Proposition 7.6.4), the facets of the apartment `g · A(S)` are the
translates `g · F`. `IsFacet`, `IsChamber` and `IsVertex` take this
description as the definition. They do not use a Tits system. It is not proved
that a subset lying in two apartments gets the same structure from both.

The predicates are not forced to agree with subgroup data. `P_x`, `K_y` and
the full fixer `G(F)_y` are kept apart: `K_y` and `G(F)_y` are defined here,
and nothing identifies them.

## What is not proved or defined

- Existence. `ValuationBuildingData G` is a type of data, not a typeclass. No
  instance or theorem says that it is inhabited for any `G`. For general
  connected reductive `G`, existence is KP's descent construction of
  Chapter 9. When `G` is quasi-split it is Definition 6.1.27. It also needs
  `Cartan.CentralizerValuationComparisonStatement` for the `bijective` field
  of `CentralizerDatum`. None of this is proved.
- Axiom V 7 (compatibility with the topology on `G(F)`) is not a field, and
  no topology on `G(F)` is used here. `ValuationBuildingAxioms` states it as
  the condition `B.IsTopologyCompatible`.
- That V 6 implies the `S(F)`-part of V 6 stored in `KPApartmentData`. Both
  are fields, so the data carry both.
- AS 5 of Axiom 4.1.6, which the corrected opening of Chapter 7 assumes. It
  is neither a field nor proved. `ValuationBuildingAxioms` states it, with
  V 6, V 7 and AS 2–AS 4, as the condition `B.SatisfiesApartmentAxioms`.
- KP's Definition 4.1.26 ("Bruhat–Tits theory is available for `G`",
  printed p. 165, PDF p. 196). In its corrected form (corrections, PDF p. 27)
  it asks for Axioms 4.1.1, 4.1.2, 4.1.4, 4.1.6, 4.1.8, 4.1.9, 4.1.16,
  4.1.17, 4.1.20 and 4.1.22, including the affine-root-system conditions
  AS 1–AS 6 of Axiom 4.1.6. Also the uniqueness of the data (Propositions
  6.2.5 and 6.2.6). `ValuationBuildingAxioms` states some of these clauses
  as conditions on `B` and proves those that hold by construction. It
  defines no combined predicate for Definition 4.1.26.
- `Z(F)^0`, `G(F)^0` and the parahoric subgroups `P_x`, `P_F`, `P_C`
  (Definitions 7.4.1(4) and 7.4.5) are not defined here. They need the
  Iwahori subgroup `Z(k)^0` and the group `G(k)^0` of Definition 2.6.23. Their
  construction uses objects that are not fields of `ValuationBuildingData`:
  over the maximal unramified extension `K`, a maximally split maximal torus
  of `Z_K` with a finite Galois splitting field; and simply connected covers
  of the derived groups of `G` and of `Z_K`. The later modules
  `KPZeroSubgroups` and `KPParahoric` define them on
  `ParahoricBuildingData G`, which extends `ValuationBuildingData G` by these
  data for the same `S` and `Z`.
- The enlarged building.
- The agreement of `IsFacet`, `IsChamber` and `IsVertex` with KP's
  Tits-system structure, and that two facets are equal or disjoint.
