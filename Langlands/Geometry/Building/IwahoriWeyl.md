# The Iwahori–Weyl group `W̃^0 = N(F)/Z(F)^0`

Module `Langlands.Geometry.Building.IwahoriWeyl`, namespace
`Langlands.Geometry.Building.ParahoricBuildingData`.

This module defines the Iwahori–Weyl group of Kaletha–Prasad and the subgroups of it that
occur in KP Theorem 7.8.1 and 7.8.2, on the actual building data
`P : ParahoricBuildingData G` of the prerequisite module `KPParahoric`. It contains only
definitions and elementary lemmas; the statements about these objects are in
`Langlands.Geometry.Building.IwahoriWeylStatement`.

## Sources

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:
  §6.6 and Definition 6.6.1 (PDF 261–262, printed 230–231); Theorem 7.5.3 and
  Proposition 7.5.5 (PDF 292, printed 261); Theorem 7.8.1 and 7.8.2 (PDF 303–304, printed 272–273).
- Kaletha–Prasad, *Corrections and additions* (1 November 2024),
  `kaletha-prasad-2024-corrections`, SHA256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`: the corrections to
  §6.6 (PDF 32: `N` is the normalizer and `Z` the centralizer of `S`) and to Theorem 7.8.1
  (PDF 35–36). The corrections do not change Definition 6.6.1, Proposition 7.5.5 or 7.8.2.

## Setting

`F` is a nonarchimedean local field (`IsNonarchimedeanLocalField F`) and
`P : ParahoricBuildingData G` is the building data of a connected reductive `F`-group `G`
with a chosen maximal split torus `i : S → G` (the structure `ParahoricBuildingData` extends
`ValuationBuildingData`). Write `N = N_G(S)`, `Z = Z_G(S)`. The module uses the following
actual objects of the Library and of `KPParahoric`:

- `normalizerPoints P.i`, the subgroup `N(F)` of `G(F)`;
- `P.centralizer.toNormalizer : Z(F) →* N(F)` and `P.centralizer.j : Z → G`;
- `P.centralizerZero`, the subgroup `Z(F)^0` of `Z(F)`;
- `P.zeroSubgroup`, the subgroup `G(F)^0` of `G(F)`;
- `P.parahoric Ω`, the subgroup `P_Ω = Z(F)^0 · G(F)^♯_Ω` (used in the statements only);
- the action of `N(F)` on the apartment `P.Apartment` (the `MulAction` of `KPApartment`)
  and the homomorphism `P.apartment.normalizerAffineEquiv` to affine automorphisms.

## Definitions

### `Z(F)^0 ⊆ N(F)` and `W̃^0`

- `normalizerZero : Subgroup (normalizerPoints P.i)` is the image of `Z(F)^0` under
  `Z(F) → N(F)`. `mem_normalizerZero_iff` says that `n ∈ N(F)` lies in it iff `n`, as an
  element of `G(F)`, lies in the image of `Z(F)^0` under `Z(F) → G(F)`.
- `IwahoriWeylGroup := normalizerPoints P.i ⧸ P.normalizerZero` is KP's
  `W̃^0 = N(k)/Z(k)^0` of §6.6 and Definition 6.6.1. It is an `abbrev` for Mathlib's type of
  left cosets of a subgroup.

KP treat `W̃^0` as a group, which presupposes that `Z(F)^0` is normal in `N(F)`. That
normality is not yet proved in the Library for the published `P.centralizerZero`. The module
therefore does not register a group instance:
every group-theoretic use of `W̃^0` below carries the instance argument
`[P.normalizerZero.Normal]`, and the statements in `IwahoriWeylStatement` assert this
normality as part of their conclusions. Likewise `G(F)/G(F)^0` is the coset type
`rationalPoints G ⧸ P.zeroSubgroup`, a group under `[P.zeroSubgroup.Normal]`.

### The affine part and the map to `G(F)/G(F)^0`

- `normalizerZeroComponent : Subgroup (normalizerPoints P.i)` is `N(F) ∩ G(F)^0`,
  i.e. `P.zeroSubgroup.subgroupOf (normalizerPoints P.i)`.
- `normalizerZero_le_normalizerZeroComponent`: `Z(F)^0 ⊆ N(F) ∩ G(F)^0`. The proof applies
  `ZeroSubgroupDatum.map_centralizerZero_le_zeroSubgroup` of `KPZeroSubgroups` through
  `mem_normalizerZero_iff`.
- `affinePart : Subgroup P.IwahoriWeylGroup` (under `[P.normalizerZero.Normal]`) is the image
  `(N(F) ∩ G(F)^0)/Z(F)^0` of `N(F) ∩ G(F)^0` in `W̃^0`. In the proof of KP Theorem 7.8.1 this
  is the kernel of `W̃^0 → G(F)/G(F)^0`, and KP Theorem 7.5.3(2) identifies it, through the
  action on `A`, with the affine Weyl group `W_aff = W(Ψ)`. The name is internal; the
  identification is part of the statement `IwahoriWeylExactSequence`, not of this definition.
- `affinePartMk : P.normalizerZeroComponent →* P.affinePart` is the surjection
  `n ↦ n Z(F)^0`, the restriction of `QuotientGroup.mk'` (Mathlib `MonoidHom.subgroupMap`).
- `normalizerZero_le_ker_toComponents` (under `[P.zeroSubgroup.Normal]`): `Z(F)^0` lies in
  the kernel of `N(F) → G(F) → G(F)/G(F)^0`, by the previous inclusion.
- `toComponents : P.IwahoriWeylGroup →* rationalPoints G ⧸ P.zeroSubgroup` (under both
  normality instances) is the homomorphism `W̃^0 → G(F)/G(F)^0` induced by `N(F) ⊆ G(F)`,
  KP's map in Theorem 7.8.1(1), obtained by `QuotientGroup.lift`. `toComponents_mk` records
  `n Z(F)^0 ↦ n G(F)^0` (by `rfl`).

### Stabilizers

- `normalizerStabilizer Ω` is the stabilizer `{n ∈ N(F) | n · Ω = Ω}` of a set `Ω` of points
  of the apartment, Mathlib's `MulAction.stabilizer` for the pointwise action on sets;
  `mem_normalizerStabilizer` unfolds it.
- `chamberStabilizer C : Subgroup P.IwahoriWeylGroup` is the image in `W̃^0` of
  `normalizerStabilizer C`. For a chamber `C` this is KP's `W̃^0_C`, the stabilizer of `C` in
  `W̃^0` (7.8.2); in the usual terminology it is the subgroup of elements of length zero for
  the Bruhat length defined by `C`, but no length function is formalized here.
- `affineFacetStabilizer Fa : Subgroup P.IwahoriWeylGroup` is the image in `W̃^0` of
  `(N(F) ∩ G(F)^0) ∩ normalizerStabilizer Fa`. For a facet `Fa` in the closure of a chamber
  this is KP's `W^aff_F` of Theorem 7.8.1(3), and
  `affineFacetStabilizer_le_affinePart` says it lies in the affine part.

## Provenance of the stabilizer definitions

KP define `W̃^0_C` as the stabilizer of `C` in `W̃^0` (7.8.2), and `W^aff_F` as the subgroup of
`W_aff` generated by the reflections in the `C`-simple affine roots vanishing on `F`;
Proposition 7.5.5 (with Lemma 1.3.17) shows that this is the stabilizer of `F` in `W_aff`.
Here both groups are defined through stabilizers in `N(F)`, which is a derived
formulation:

- `W̃^0` acts on `A` through `N(F)` only once `Z(F)^0` acts trivially, which is part of the
  identification in Theorem 7.8.1(1). Taking the image in `W̃^0` of the stabilizer in `N(F)`
  needs no such action and agrees with KP's stabilizer once it exists, because then the
  class of `n` stabilizes `C` iff `n` does.
- `W^aff_F` is defined by the stabilizer characterization of Proposition 7.5.5, transported
  along KP's identification `(N(F) ∩ G(F)^0)/Z(F)^0 = W_aff` (Theorem 7.5.3(2)). The
  generator description by `C`-simple affine roots is not formalized here.

The definitions make sense for every subset `C` or `Fa` of the apartment; the restriction to
chambers and to facets of a common chamber is imposed in the statements.

`AffineRootSystem.affineWeylGroup P.affineRoots`, the "abstract" affine Weyl group `W(Ψ)`
generated by the affine reflections, is a separate published object and is not redefined.
