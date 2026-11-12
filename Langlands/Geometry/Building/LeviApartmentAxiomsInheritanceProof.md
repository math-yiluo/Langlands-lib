# Proof that the apartment axioms pass to a standard Levi subgroup

`Langlands.Geometry.Building.leviApartmentAxiomsInheritance` proves
`LeviApartmentAxiomsInheritanceStatement.{u}` at an arbitrary universe `u`.
Take apartment data `D` of `(G, S)` satisfying V 6, V 7 and AS 2–AS 5 for `C`.
If some point of the apartment data `DM` of the standard Levi
`(M_J, S)` restricts some point of `D`, then `DM` satisfies the same axioms
for any centralizer datum `CM` of `S` in `M_J`.

## Helper modules

The proof uses five new modules, listed in the candidate's repository paths:

- `Langlands.Geometry.Building.AffineRootSystemPullback`: affine root systems
  detected by pullback along a surjective affine map;
- `Langlands.Geometry.Building.NormalizerImageAffineWeylBounds`: the first
  sentence of AS 5 from AS 3, AS 4 and V 6, for `ValuationBuildingData`;
- `Langlands.BruhatTits.SpecialCompact.LeviApartmentAxioms`: V 7, AS 2–AS 4,
  and the second and third sentences of AS 5 for a same-roots Levi, all for
  the restricted class `leviRestrictedApartmentData`;
- `Langlands.Geometry.Building.LeviRestrictionCompatibility` (by Worker 119):
  one restriction pair identifies `DM` with the restricted class, V 6 for an
  arbitrary `CM`, and the semisimple case of a dynamic Levi;
- this module.

## The dynamic-centralizer step

Let `j : M → G` represent the dynamic centralizer of a cocharacter `ζ` of
`S`, with `iM ≫ j = i`. Write `DM` for `leviRestrictedApartmentData` of `D`.

`relativeRoots_levi_eq_of_cocharacter_eq_zero` shows that if `ζ = 0`, then
`relativeRoots iM = relativeRoots i`, by `relativeRoots_centralizer_factor`.

`satisfiesApartmentAxioms_leviRestricted` assumes that `M` is connected
reductive, that `iM` is a maximal split torus, and that V 6 holds for `DM` and
`CM`. It concludes `DM.SatisfiesApartmentAxioms CM`. Field by field:

- **V 6** is the hypothesis.
- **V 7** is `isTopologyCompatible_levi` applied to V 7 for `D`.
- **AS 2 and AS 3** are `isAffineRootSystem_levi` for `Ψ′` and `Ψ`, with the
  membership criteria `mem_extendedAffineRoots_levi_iff` and
  `mem_affineRoots_levi_iff`. The derivative condition is read off the
  definition of (extended) affine roots.
- **AS 4** is `mem_or_two_smul_mem_levi`.
- **AS 5, first sentence.** The proof builds valuation building data
  `B : ValuationBuildingData M` from `M`, `iM`, `DM`, `CM` and V 6. Then
  `B.affineWeylGroup_le_range_of_AS3` (with AS 3 for `DM`) gives
  `W(Ψ_M) ≤` image, and `B.range_le_extendedAffineWeylGroup_of_AS4` (with
  AS 4 for `DM`) gives image `≤ W(Ψ_M)ᵉˣᵗ`.
- **AS 5, second sentence.** Let `M` be simply connected. Then `M` is
  semisimple. `cocharacter_eq_zero_of_isSemisimple_levi` gives `ζ = 0`, and
  `exists_leviIso_of_isSemisimple` gives an isomorphism `e : M ≅ G`. So `G`
  is simply connected (`IsSimplyConnected.of_iso`), and AS 5 for `D` gives
  that the image of `N_G(F)` is `W(Ψ_G)`. Since `ζ = 0` the roots agree, and
  `range_eq_affineWeylGroup_levi` with the lower bound above gives that the
  image of `N_M(F)` is `W(Ψ_M)`.
- **AS 5, third sentence.** Let `M` be quasi-split and adjoint. Then `M` is
  semisimple, so `ζ = 0`. `exists_leviIso_of_isSemisimple` gives `e`, and
  `isIso_leviHom_of_isSemisimple` gives `IsIso j`. `G` is quasi-split and
  adjoint by `IsQuasiSplit.of_iso` and `IsAdjoint.of_iso`, so the image of
  `N_G(F)` is `W(Ψ_G)ᵉˣᵗ`. `range_eq_extendedAffineWeylGroup_levi` with the
  upper bound above gives that the image of `N_M(F)` is `W(Ψ_M)ᵉˣᵗ`.

## The standard Levi

`leviApartmentAxiomsInheritance` introduces the data of the statement and
installs these instances:

- affineness of `G` (`IsConnectedReductive.isAffineHom`) and of `M_J`
  (`Standard.isClosedSubgroup_leviHom`);
- the monomorphisms of `i` and of `iM = Standard.leviTorusHom i ν J`, which is
  a maximal split torus by `Standard.isMaximalSplitTorus_leviTorusHom`;
- smoothness and connectedness of `G`;
- smoothness of `M_J`, from `standardLeviSplitComponentStatement`.

The proof then proceeds as follows.

1. `StandardLeviSplitComponent.exists_standardLevi_eq_dynamicCentralizer`
   gives `ζ` with `standardLevi i ν J` equal to the dynamic centralizer of
   `ζ`. With `Standard.isRepresentedBy_leviHom`, the inclusion
   `j = Standard.leviHom i ν J` represents that centralizer.
2. V 6 for `DM` and the arbitrary `CM` is
   `isOmegaCompatible_standardLevi_of_pair`, applied to the restriction pair
   and V 6 for `D`.
3. `eq_leviRestrictedApartmentData_of_pair` identifies `DM` with
   `leviRestrictedApartmentData` of `D`; the proof substitutes it.
4. `satisfiesApartmentAxioms_leviRestricted` concludes. It uses
   `Standard.leviTorusHom_comp`, `Standard.isClosedSubgroup_leviHom` and
   `standardLevi_isConnectedReductive` (module `LeviApartmentComparison`).

## Relation to the source

The statement is derived from Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), §6.7 (Lemma 6.7.1, §6.7.2), Definition 6.1.2 and
Axiom 4.1.6 with Remark 4.1.7, as described in the statement's Markdown. The
route matches its expected outline in two places. AS 2–AS 4 come from those
of `D` through the projection of apartments (§6.7.2). The first sentence of
AS 5 follows from AS 3, AS 4 and V 6, as in Remark 4.1.7.

The route differs in one place. The statement's Markdown observes that
`M_J` is semisimple only when `M_J = G`, by a dimension count of the central
torus. The proof instead uses the vanishing of `ζ` and the resulting
isomorphism `M_J ≅ G`, and transports AS 5 from `D` along the bijective
projection of apartments.
