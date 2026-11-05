# Axioms 4.1.9 and 4.1.16: the Tits system and the Iwahori decomposition

This module states KP Axiom 4.1.9 (the Iwahori–Tits system) and KP Axiom 4.1.16 (the Iwahori
decomposition) for the Library's parahoric building data. It is part of the full corrected
Definition 4.1.26 predicate (task `129deca1-ce21-411b-9b79-7e94545fe26d`). It contains
definitions of subgroups and product maps, two validity predicates with their whole-apartment
forms `HasTitsSystem` and `HasIwahoriDecomposition`, and lemmas that unfold or follow directly
from these predicates. Nothing here asserts that the predicates hold for given data, or that
data exist.

Ambient setting: `F` is a nonarchimedean local field in universe `u`, `G` is a group scheme
over `Spec F` with `[IsAffineHom G.X.hom]`, and `P : ParahoricBuildingData G` is the Library's
building datum. It has maximal split torus `i : S → G` (`P.i`), normalizer points
`N(F) = normalizerPoints P.i`, centralizer datum `Z = P.centralizer.Z` with inclusion
`P.centralizer.j : Z → G`, apartment `A(S) = P.Apartment`, map `P.apartmentMap : A(S) → B(G)`
into the reduced building `B(G) = P.ReducedBuilding`, and the groups `G(F)^0 = P.zeroSubgroup`
and `Z(F)^0 = P.centralizerZero` (KP Definition 2.6.23).

Source: T. Kaletha and G. Prasad, *Bruhat–Tits theory: a new approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. Page numbers are PDF pages of that file, with
the printed page in parentheses. Axiom 4.1.9 is on PDF 192 (p. 161), Axiom 4.1.16 on PDF 193
(p. 162), and Definition 4.1.3 on PDF 189 (p. 158). The 2024 corrections
(`kaletha-prasad-2024-corrections`, PDF 27) change Axiom 4.1.9 in two places. After "`B(G)`"
they add "(`B(G)` as in Axiom 4.1.1)". In the last sentence they replace "is precisely the
parabolic subgroup" by "is a parabolic subgroup". They do not change Axiom 4.1.16 or
Definition 4.1.3.

## Declarations

All declarations below are in the namespace `Langlands.Geometry.Building.ParahoricBuildingData`
unless they start with `TitsSystem.`, which means `Langlands.Group.TitsSystem`.

| Lean declaration | Source | Content |
|---|---|---|
| `TitsSystem.subset_standardParabolic` (theorem) | KP Definition 1.4.4(1), PDF 79 (p. 48) | `B ⊆ G_X = B W_X B` for every `X`. |
| `TitsSystem.IsAdmissibleParabolic.isParabolic` (theorem) | KP Definition 1.4.4(2), PDF 79 (p. 48) | An admissible parabolic subgroup `g G_X g⁻¹` contains `g B g⁻¹`, so it is parabolic. |
| `zeroStabilizer P Y` | KP Definition 4.1.3, PDF 189 (p. 158) | `G(F)^0_Y = G(F)^0 ⊓ stabilizer of Y`, for `Y ⊆ B(G)`, as a subgroup of `G(F)`. `mem_zeroStabilizer` unfolds it. |
| `zeroStabilizerIn P Y` | same | The same group as a subgroup of `G(F)^0`. `map_zeroStabilizerIn` and `mem_zeroStabilizerIn` compare the two forms. |
| `normalizerInZero P` | KP Axiom 4.1.9, PDF 192 (p. 161) | `N = N(F) ∩ G(F)^0`, as a subgroup of `G(F)^0`. |
| `facetZeroStabilizer P Fc` | KP Definition 4.1.3(1) | The parahoric subgroup `G(F)^0_F` of a facet `F` of `B(G)`, as a subgroup of `G(F)^0`. |
| `chamberZeroStabilizerIn P Ca` | KP Definition 4.1.3(2) | The Iwahori subgroup `I = G(F)^0_C`, where `C` is the image in `B(G)` of the chamber `Ca` of `A(S)`, as a subgroup of `G(F)^0`. |
| `apartmentFacetStabilizers P` | KP Proposition 1.5.6(6), PDF 87 (p. 56); Remark 1.5.7, PDF 89–90 (pp. 58–59) | For each apartment `h · A(S)` of `B(G)` (`h ∈ G(F)`), the set of the groups `G(F)^0_F` for the facets `F ⊆ h · A(S)`. |
| `IsBuildingTitsSystem P Ca π Sgen` (structure) | KP Axiom 4.1.9 as corrected | See below. |
| `HasTitsSystem P` | same | For every chamber `Ca` of `A(S)` there are `W : Type u`, a group structure on `W`, `π : N →* W` and `Sgen ⊆ W` with `IsBuildingTitsSystem P Ca π Sgen`. |
| `IsBuildingTitsSystem.isParabolic_facetZeroStabilizer` (theorem) | corrected last sentence of Axiom 4.1.9 | Each `G(F)^0_F` is a parabolic subgroup of the Tits system. |
| `IsBuildingTitsSystem.exists_facetZeroStabilizer_eq` (theorem) | KP Remark 4.1.11, PDF 192 (p. 161) | Each admissible parabolic subgroup is some `G(F)^0_F`. |
| `zeroStabilizerUnipotentPoints P ν Y` | KP Axiom 4.1.16, PDF 193 (p. 162) | `U(ν)(F) ∩ G(F)^0_Y`, where `U(ν)` is the Library's Dynamic unipotent subgroup functor `Dynamic.unipotent` of the cocharacter `ν` of `S` composed with `i`. |
| `zeroStabilizerProduct P Y ν` | same | `(u, z, v) ↦ u · j(z) · v` on `(U(ν)(F) ∩ G(F)^0_Y) × Z(F)^0 × (U(-ν)(F) ∩ G(F)^0_Y)`, with values in `G(F)`. |
| `IsLeastNonnegativeFunctional P α Ω ψ` | same | `ψ : A(S) →ᵃ[ℝ] ℝ` has derivative `α` (`ψ.linear = rootForm P.i α`), is non-negative on `Ω`, and is pointwise at most every other such functional. |
| `orderedAffineRootProduct P a ψ` | same | `(u_j) ↦ u_0 u_1 ⋯ u_{n-1}` on `∏_j U_{ψ(a_j)}`, for roots `a_0, …, a_{n-1}` and functionals `ψ(a_j)`. `U_ψ` is the Library's `affineRootGroup` (KP Definition 6.3.1). |
| `IsOrderedRootProductBijective P Ca ν` | same, second sentence | For the least functionals `ψ_a` and every injective enumeration `a_0, …, a_{n-1}` of the non-divisible roots positive on `ν`, the ordered product is injective with image `U(ν)(F) ∩ I`. |
| `IsIwahoriDecompositionAt P Ca ν` (structure) | KP Axiom 4.1.16 | See below. |
| `HasIwahoriDecomposition P` | same | `IsIwahoriDecompositionAt P Ca ν` for every chamber `Ca` of `A(S)` and every generic cocharacter `ν` (`IsGenericCocharacter P.i ν`). |
| `IsIwahoriDecompositionAt.map_centralizerZero_le` (theorem) | consequence of the first sentence of Axiom 4.1.16 | `j(Z(F)^0) ≤ I`. |
| `IsLeastNonnegativeFunctional.unique` (theorem) | the word "smallest" in Axiom 4.1.16 | The least functional is unique. |
| `IsLeastNonnegativeFunctional.affineRootGroup_le_rootFixer` (theorem) | KP Definition 7.4.1(1) | `U_{ψ_a} ≤ U_{a,Ω,0}` (the Library's `rootFixer`), from the Library lemma `affineRootGroup_le_rootFixer`. |

## Axiom 4.1.9

KP: let `A` be the apartment of `B(G)` (as in Axiom 4.1.1) attached to a maximal split torus
`S`, and let `C ⊆ A` be a chamber. Put `G = G(k)^0`, `I = G(k)^0_C` and `N = N(k) ∩ G`. Then
`(I, N)` is a saturated Tits system in `G` whose restricted building is `B(G)`. In other words,
the stabilizer `G(k)^0_F` of a facet `F` is a parabolic subgroup of this Tits system.

`IsBuildingTitsSystem P Ca π Sgen` has six fields. Here `I = chamberZeroStabilizerIn P Ca` and
`N = normalizerInZero P`, both subgroups of `G(F)^0`.

| Field | Content | Source |
|---|---|---|
| `isTitsSystem` | `IsTitsSystem I N π Sgen`: the Library's Tits-system predicate (TS 1–TS 4), with Weyl group `W` given by the surjection `π : N →* W` with kernel `I ∩ N` | KP Definition 1.4.1, PDF 78 (p. 47) |
| `finite` | `Sgen` is finite | KP Proposition 1.5.6 and Definitions 1.5.17–1.5.20 assume this, PDF 87–93 (pp. 56–62) |
| `isSaturated` | TS 5: `⋂_{n ∈ N} n I n⁻¹ = I ∩ N` (`TitsSystem.IsSaturated`) | KP Definition 1.4.1, PDF 78 (p. 47) |
| `bijOn_facetZeroStabilizer` | `F ↦ G(F)^0_F` is a bijection from all facets of `B(G)` onto the admissible parabolic subgroups (`TitsSystem.IsAdmissibleParabolic`) | KP Proposition 1.5.6(2), Remark 1.5.7, Proposition 1.5.18(1), Definition 1.5.20, PDF 87–93 |
| `facetPrecedes_iff` | `F ≺ F'` (Library `FacetPrecedes`, `F` is a face of `F'`) iff `G(F)^0_{F'} ≤ G(F)^0_F` | KP Proposition 1.5.6(2), Remark 1.5.7 |
| `apartmentFacetStabilizers_eq` | `apartmentFacetStabilizers P = TitsSystem.restrictedApartments I π Sgen` | KP Proposition 1.5.6(6), Proposition 1.5.18(1), Definition 1.5.20 |

*The restricted building is `B(G)`.* KP Remark 1.5.7 reads the building of a Tits system as the
set of its proper parabolic subgroups, with the face relation reversed. In this reading the
facet `F` of the Tits building is the parabolic subgroup `P_F` (Proposition 1.5.6(2)), and
`P_F` is the stabilizer of `F` (Proposition 1.5.13(2), PDF 91 (p. 60)). The restricted
building (Proposition 1.5.18, Definition 1.5.20) is the subcomplex of admissible facets, with
apartments `B' ∩ g A`. `TitsSystemRestricted.md` explains these definitions. The axiom
identifies `B(G)` with this restricted building `G(F)^0`-equivariantly. Under such an
identification a facet `F` of `B(G)` and the facet of the restricted building it corresponds to
have the same stabilizer in `G(F)^0`, and the stabilizer of a facet of the restricted building
is the corresponding admissible parabolic subgroup. So the identification is
`F ↦ G(F)^0_F`. The predicate states that this map is a bijection onto the admissible
parabolic subgroups, turns the face relation into reverse inclusion, and turns the apartments
of `B(G)` into the apartments of the restricted building. These three clauses are the
combinatorial content of "the restricted building is `B(G)`". The facets, the face relation and
the apartments of `B(G)` are those of Axiom 4.1.1 in the Library: `BuildingFacet`,
`FacetPrecedes` (from `Langlands.BruhatTits.IntegralModels.FacetParabolicOrder`) and the
translates `h · A(S)` of `P.apartmentImage`.

*Corrected wording.* The original last sentence says that `G(k)^0_F` "is precisely the"
parabolic subgroup. The correction replaces this by "is a" parabolic subgroup. The predicate
does not use the parabolic-subgroup property as a field. It states the identification of the
buildings, from which `isParabolic_facetZeroStabilizer` derives the corrected sentence:
`G(F)^0_F` contains a conjugate of `I`.

*Stabilizer, not pointwise fixer.* KP Definition 4.1.3 defines `G(k)^0_F` as the stabilizer of
`F` in `G(k)^0`. `zeroStabilizer` is this setwise stabilizer. KP 4.1.12(1) derives from
Axiom 4.1.9 that it equals the pointwise stabilizer, but that is a consequence, not part of the
definition. The Library's `P.zeroFixer Ω` (pointwise, used for Axioms 4.1.8 and 4.1.20) and
`P.parahoric Ω` (KP Definition 7.4.1, used by `chamberIwahori` in
`Langlands.Geometry.Building.ChamberIwahori`) are different definitions. This module does not
compare them with `zeroStabilizer`.

*The group `W`.* KP's Weyl group is `N/(I ∩ N)`. The predicate quantifies over a group `W` in
universe `u` and a surjection `π : N →* W` with kernel `I ∩ N` (fields `surjective` and `ker_eq`
of `IsTitsSystem`). This determines `W` up to the isomorphism `N/(I ∩ N) ≅ W`, which also
matches `Sgen` with KP's `S`.

*An empty `Sgen`.* KP Definition 1.5.17 assumes `S` finite and non-empty. The predicate
requires `Sgen` finite but allows `Sgen = ∅`. Then `W` is trivial, `I = G(F)^0`, the only
admissible type is `∅`, and the restricted building has the single facet `I`. This is what
happens when `G` has no relative roots, so that `G` is anisotropic modulo its centre and `B(G)`
is a point. KP's definitions do not cover this case. The predicate extends them in this way.

*Which tori and chambers.* KP quantifies over every maximal split torus `S` and every chamber
of its apartment. The predicate is stated for the base torus `S` of `P` and every chamber `Ca`
of the affine root system of `A(S)` (`AffineRootSystem.IsChamber P.affineRoots Ca`), whose image
`P.apartmentMap '' Ca` is a chamber of `B(G)` in `A(S)` (Library `IsChamber`). Other maximal
split tori and their apartments are `G(F)`-conjugates of `S` and `A(S)` (Axiom 4.1.1, as stated
in `Langlands.Geometry.Building.FullValidity.Realization`). The Library's
`ParahoricBuildingData` states Axioms 4.1.6 and 4.1.8 at the base torus in the same way. The
transport of the statement to other tori by conjugation is not formalized here.

## Axiom 4.1.16

KP: let `S` be a maximal split torus with apartment `A`, `C ⊆ A` a chamber and `I = G(k)^0_C`.
For any positive system `Φ^+ ⊆ Φ(S, G)`, the product map
`(U^+(k) ∩ I) × Z(k)^0 × (U^-(k) ∩ I) → I` is bijective. Here `U^+` is the unipotent radical of
the minimal parabolic subgroup containing `S` attached to `Φ^+`, and `U^-` is that of the
`S`-opposite parabolic subgroup. Moreover, the product map `∏_{a ∈ Φ^{±,nd}} U_{ψ_a} → U^±(k) ∩ I`
is a bijection for the product in any order. Here `ψ_a` is the smallest affine functional on
`A` with derivative `a` that is non-negative on `C`.

`IsIwahoriDecompositionAt P Ca ν` has five fields. Here `I = zeroStabilizer P (apartmentMap '' Ca)`,
`U^+ = U(ν)` and `U^- = U(-ν)`.

| Field | Content |
|---|---|
| `injective_product` | `(u, z, v) ↦ u · j(z) · v` is injective on `(U(ν)(F) ∩ I) × Z(F)^0 × (U(-ν)(F) ∩ I)` |
| `range_product` | its image is `I` |
| `exists_isLeastNonnegativeFunctional` | for every non-divisible root `a`, the least functional `ψ_a` exists |
| `orderedProduct_pos` | `IsOrderedRootProductBijective P Ca ν`: `∏_{a ∈ Φ^{+,nd}} U_{ψ_a} → U(ν)(F) ∩ I` is bijective in every order |
| `orderedProduct_neg` | `IsOrderedRootProductBijective P Ca (-ν)`: `∏_{a ∈ Φ^{-,nd}} U_{ψ_a} → U(-ν)(F) ∩ I` is bijective in every order |

The first two fields together say that the product map is a bijection onto `I`.

*Positive systems.* A positive system of `Φ(S, G)` is written as `{a | ⟨a, ν⟩ > 0}` for a
generic cocharacter `ν` (`IsGenericCocharacter P.i ν`: `⟨a, ν⟩ ≠ 0` for every relative root
`a`). Every positive system has this form, because an open Weyl chamber in `ℝ ⊗ X_*(S)` contains
a rational point and hence, after scaling, a point of `X_*(S)`. Conversely the roots positive on
a generic `ν` form a positive system. Quantifying over all generic `ν` therefore covers every
positive system, some of them more than once. The negative system is that of `-ν`.
`RelativeRoot.indivisiblePositiveRoots P.i ν` is the set `Φ^{+,nd}` of non-divisible roots `a`
with `⟨a, ν⟩ > 0`, and `RelativeRoot.indivisibleRoots P.i` is the set of all non-divisible
roots.

*The unipotent radicals.* `U(ν)` is the Library's dynamic unipotent subgroup functor
`Dynamic.unipotent` of `ν` composed with `i`. This is the dynamic construction of Conrad, Gabber
and Prasad, *Pseudo-reductive groups* (2015, registered as
`conrad-gabber-prasad-2015-pseudo-reductive`), §2.1. For generic `ν`, the dynamic parabolic
`P(ν)` is the minimal parabolic subgroup containing `S` attached to the positive system of `ν`,
`U(ν)` is its unipotent radical, and `P(-ν)` is the `S`-opposite parabolic. This standard
identification is not proved here. The Library's `iwahoriUnipotentPoints` (in
`Langlands.Geometry.Building.ChamberIwahori`) uses the same convention. That definition
intersects with the Chapter 7 group `chamberIwahori`. This module intersects with the
Definition 4.1.3 group `zeroStabilizer`.

*Order of the three factors.* The map has the order of KP, `U^+ × Z^0 × U^-`, for the positive
system of `ν`. The order `U^- × Z^0 × U^+` is the same statement for `-ν`, which is also generic.
KP's remark after the axiom says that the order of the three factors does not matter.

*The functionals `ψ_a`.* KP's "affine functional on `A` with derivative `a`" is an affine map
`ψ : A(S) → ℝ` with `ψ.linear = rootForm P.i a`. Two such maps differ by a constant, so they are
totally ordered pointwise and "smallest" has its pointwise meaning
(`IsLeastNonnegativeFunctional`). The least one is unique (`IsLeastNonnegativeFunctional.unique`).
KP takes its existence for granted. The field `exists_isLeastNonnegativeFunctional` states it,
so that the ordered-product clauses are not vacuous. The functionals are not required to be
affine roots. `U_ψ` is defined for every affine functional with derivative `a` (KP
Definition 6.3.1, Library `affineRootGroup`), as `U_{a,x,ψ(x)}` for any `x ∈ A(S)`. Its elements
lie in `rootGroupPoints P.i a`, the rational points of the Library's relative root subgroup
`U_a`.

*Any order.* An order of the factors is an injective map `a : Fin n → Φ` whose image is
`Φ^{+,nd}` (respectively `Φ^{-,nd}`). `orderedAffineRootProduct` multiplies one element of each
`U_{ψ_{a_j}}` in the order `j = 0, 1, …, n-1`. `IsOrderedRootProductBijective` asks, for every
such enumeration, that this map be injective with image `U(±ν)(F) ∩ I`. It quantifies over the
family `ψ` of least functionals, which is unique on non-divisible roots.

*Which tori and chambers.* As for Axiom 4.1.9, the predicate is stated for the base torus `S`
and every chamber `Ca` of `A(S)`.

## Use

The assembled Definition 4.1.26 predicate (a later unit of the same task) uses `HasTitsSystem`
for Axiom 4.1.9 and `HasIwahoriDecomposition` for Axiom 4.1.16. Axioms 4.1.2, 4.1.6 and 4.1.8 are
taken from the fields of the Library's `SatisfiesPartialBuildingAxioms`.
