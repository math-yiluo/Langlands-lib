# Kaletha–Prasad axioms on building data

Module `Langlands.Geometry.Building.ValuationBuildingAxioms`, namespace
`Langlands.Geometry.Building.ValuationBuildingData`.

Worker 1238's published `ValuationBuildingData G` (module `ValuationBuildingData`) bundles, for a
connected reductive `G` over a nonarchimedean local field `F`, a maximal split torus `S`, an
`N(F)`-stable class `A(S)` of valuations of the root datum, the actual centralizer `Z = Z_G(S)`
and the axiom V 6 on `Z(F)`. From these data it builds the apartment `A = A(S)` and the reduced
building `B(G)` of KP (7.6.2) with its `G(F)`-action. It also gives the affine roots, the facets
of the apartment and of the building, and the fixers.

This module states on `B : ValuationBuildingData G` the clauses of the corrected KP
Definition 4.1.26 that can be written with the objects of `B` alone. It proves the clauses that
hold by construction. The predicates are conditions on `B`. Nothing here asserts that they hold
for given data, or that data exist; that is KP's construction (Chapters 6, 7 and 9).

## Setting

- `F` is a field with `[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`.
- `G : GroupScheme (Spec (CommRingCat.of F))` with `[IsAffineHom G.X.hom]`.
- `B : ValuationBuildingData G`. Its fields used here are `B.i : S → G` (the maximal split
  torus), `B.apartment : KPApartmentData B.i (localFieldOrder F)` (the class `A(S)`),
  `B.centralizer : CentralizerDatum B.i` (the actual `Z`, with `j : Z → G`) and
  `B.isOmegaCompatible` (V 6 on `Z(F)`).
- The apartment `B.Apartment` is an affine space over `TranslationSpace B.i`, which is `V(S)`
  modulo the common kernel of the roots. KP write `V′ = V(S′)` for this space. The building is
  `B.ReducedBuilding`, and `B.apartmentMap : B.Apartment → B.ReducedBuilding` is the map
  `x ↦ [1, x]`.
- `G(F)` is `rationalPoints G`, `N(F)` is `normalizerPoints B.i`, and `G(F)^1` is
  `Plancherel.rationalCommonNormKernel G` (KP Notation 2.6.15). The scoped `MonObj` instances
  give the group structure on `rationalPoints G`.

## The axioms on the apartment class, and Axiom 4.1.2

These declarations restate published predicates for `B`.

- `B.IsTopologyCompatible` is `B.apartment.IsTopologyCompatible`. It is KP axiom V 7
  (Definition 6.1.2, book PDF p. 230) for every valuation of the class `A(S)`, from the published
  module `KPApartmentAxioms`.
- `B.SatisfiesApartmentAxioms` is `B.apartment.SatisfiesApartmentAxioms B.centralizer`, the
  published structure from `KPApartmentAxioms` for the actual centralizer of `B`. It collects
  V 6 on `Z(F)`, V 7, and AS 2–AS 5 of KP Axiom 4.1.6 (book PDF pp. 190–191) for the published
  sets `Ψ′ = B.apartment.extendedAffineRoots` and `Ψ = B.affineRoots`. The Markdown of
  `KPApartmentAxioms` explains the provenance of each field.
- `satisfiesApartmentAxioms_iff` (proved). V 6 is the field `B.isOmegaCompatible` of the data.
  So `B.SatisfiesApartmentAxioms` is equivalent to the conjunction of the other fields: V 7; AS 2
  and AS 3 (`Ψ′` and `Ψ` are affine root systems with derivative set `Set.range (rootForm B.i)`,
  which is `Φ`; "affine root system" is the published `IsAffineRootSystemWithRankZero` of the
  module `RankZeroAffineRootSystem`, whose AR 1 admits KP's rank-zero system `∅`); AS 4; the inclusions `W(Ψ) ≤ f(N(F)) ≤ W(Ψ)ᵉˣᵗ`; `f(N(F)) = W(Ψ)` if `G` is
  simply connected; and `f(N(F)) = W(Ψ)ᵉˣᵗ` if `G` is quasi-split and adjoint. Here `f` is the
  action map below.
- `B.HasBoundedOpenStabilizers` is `B.apartment.HasBoundedOpenStabilizers`. It is KP Axiom 4.1.2
  (book PDF p. 189, printed p. 158), "the stabilizer `G(k)^1_x` of a point `x ∈ B(G)` for the
  action of `G(k)^1` is a bounded open subgroup of `G(k)`". The predicate asks this for every
  point `y` of `B.ReducedBuilding`: `K_y = G(F)^1 ⊓ G(F)_y` is open for the published
  `rationalPointTopology F G.X`, and it is bounded in the sense of KP Definition 2.2.1.

## Axiom 4.1.4 (A 1): the action of `N(F)` on the apartment

KP Axiom 4.1.4 (A 1) (book PDF p. 190, printed p. 159): "The action of `N(k)` on `A` is by affine
transformations. Let `f : N(k) → Aff(A)` be the action map […]. For `n ∈ N(k)`, the derivative
`df(n) ∈ Aut(V′)` is the automorphism of `V′` induced by the action of `N(k)` on `X_*(S′)` […]. In
particular, the group `Z(k)` acts on `A` by translations, where the translation `ν(z) ∈ V′` for
`z ∈ Z(k)` is the image under `V(S) → V(S′)` of `−ω_Z(z)` […]."

In the data `B` these hold by construction, and the module proves them.

- `B.normalizerAction : normalizerPoints B.i →* (B.Apartment ≃ᵃ[ℝ] B.Apartment)` is the action
  map `f`. It is the published `normalizerAffineEquiv` of the class `A(S)`.
- `normalizerAction_apply`: `f(n)(x) = n • x`, the published action of `N(F)` on the apartment.
- `normalizerAction_linear`: the linear part of `f(n)` is `translationAction B.i n`. This is the
  action of `n` on `TranslationSpace B.i` induced by its published action on `V(S)`. KP state
  it for `X_*(S′)` and `V′ = V(S′)`; the Library's `TranslationSpace` is the quotient of `V(S)`
  that KP identify with `V(S′)`, and that identification is not made here.
- `normalizerAction_centralizer`: for `z ∈ Z(F)`, `f(z)` is the translation by the class of
  `ν(z) = B.translation z`. The published `B.translation` is `ν = −ω_Z`. The proof is the
  published `IsOmegaCompatible.normalizerAffineEquiv_eq` applied to V 6 of `B`.
- `normalizerAction_centralizer_eq_one`: elements of `Z(F)^1 = ker ν` (as
  `rationalCommonNormKernel B.centralizer.Z`) act trivially. KP state this for the maximal
  bounded subgroup `Z(k)_b`. The identification of `Z(k)_b` with `Z(F)^1` is not in the Library,
  so the lemma is stated for `Z(F)^1`.

A 0 holds because the apartment is by definition an affine space over `TranslationSpace B.i`. A 2
concerns the maps `A(S) → A(gSg⁻¹)` between the apartments of different tori. In these data the
other apartments are the translates `g · A(S)` inside the building (next section), so A 2 is not
a separate condition and is not stated.

## Axiom 4.1.8 (1): `U_ψ` fixes a half-apartment

KP Axiom 4.1.8 (1) (book PDF p. 191, printed p. 160): "The action of `U_ψ` on `B` fixes the
half-apartment `A_{ψ≥0}`." For the reduced building of a valuation this is KP Fact 7.6.7 (book
PDF p. 297, printed p. 266), "immediate from (7.6.2)".

`affineRootGroup_le_pointwiseFixer` (proved): let `α` be a relative root and `ψ` an affine
function on the apartment whose linear part is `rootForm B.i α`. Then

`B.affineRootGroup α ψ ≤ B.pointwiseFixer (B.apartmentMap '' {x | 0 ≤ ψ x})`.

The statement is for every such `ψ`, not only for `ψ ∈ Ψ`. KP define `U_ψ` for every such `ψ`
(AS 3, Definition 6.3.1).

Proof. Take `u ∈ U_ψ` and `x` with `ψ(x) ≥ 0`. By the published `affineRootGroup_eq_filtration`,
`U_ψ = U_{α,x,ψ(x)}`, and this filtration is antitone in the index, so `u ∈ U_{α,x,0}`. The
published lemmas `rootFixer_singleton` and `rootFixer_le_sharpFixer` put `U_{α,x,0}` inside
`G(F)^♯_x`, and `sharpFixer_le_fixer` says that `G(F)^♯_x` fixes `[1, x]`. This is the route of
KP's proof through the relation (7.6.2).

## Apartments and the stabilizer clause of Axiom 4.1.1

KP Axiom 4.1.1 (book PDF pp. 188–189, printed pp. 157–158) asks for a building `B(G)` in the sense
of Definition 1.5.5 with a `G(k)`-action whose apartments correspond bijectively and
`G(k)`-equivariantly to the maximal split tori. "In particular, the stabilizer in `G(k)` of an
apartment `A = A(S)` corresponding to a maximal `k`-split torus `S` is `N(k)`."

- `B.apartmentImage : Set B.ReducedBuilding` is `Set.range B.apartmentMap`, the apartment of
  `S` in the building.
- `B.IsApartment Y` means `∃ g : G(F), Y = g • B.apartmentImage`. This defines the apartments of
  `B(G)` as the `G(F)`-translates of `A(S)`. Derived definition: in KP the apartments correspond
  `G(k)`-equivariantly to the maximal split tori (Proposition 7.6.3 (1) and Corollary 7.6.9, book
  PDF pp. 295–297), so `g · A(S)` is the apartment of `g S g⁻¹`. The maximal split tori form one
  `G(k)`-conjugacy class, so the apartments are exactly the translates `g · A(S)`. The Lean
  definition uses this description and does not refer to other maximal split tori.
- Proved: `isApartment_apartmentImage`, `IsApartment.smul` (the apartments are permuted by
  `G(F)`) and `exists_isApartment_mem` (every point lies in an apartment, from the published
  `exists_smul_apartmentMap`).
- `normalizerPoints_le_stabilizer_apartmentImage` (proved): `N(F)` stabilizes `A(S)`, from the
  published `normalizer_smul_apartmentMap`.
- `B.HasNormalizerApartmentStabilizer` is the condition
  `MulAction.stabilizer (rationalPoints G) B.apartmentImage = normalizerPoints B.i`. This is the
  quoted clause. KP prove it for their construction in Proposition 7.6.8 (book PDF p. 297, printed
  p. 266), using Fact 2.6.22, which is not in the Library. So here it is a condition.
- `hasNormalizerApartmentStabilizer_iff` (proved): the condition holds if and only if every `g`
  with `g • A(S) = A(S)` lies in `N(F)`. The other inclusion is the previous lemma.
- `HasNormalizerApartmentStabilizer.smul_apartmentImage_eq_iff` (proved): under the condition,
  `g • A(S) = A(S) ↔ g ∈ N(F)`.

Under the condition, `g S g⁻¹ ↦ g · A(S)` is a well-defined injective map from the
`G(F)`-conjugates of `S` onto the apartments, because `g S g⁻¹ = h S h⁻¹` exactly when
`h⁻¹ g ∈ N(F)`. This remark is not formalized: the Library has no type of conjugates of `S`.

## AS 6

AS 6 of KP Axiom 4.1.6 (book PDF p. 191, printed p. 160): "The polysimplicial structure on `A`
endowed by the affine root hyperplanes of `Ψ` (equivalently `Ψ′`) as in Remark 1.3.16 coincides
with the polysimplicial structure coming from `B`."

`B.HasCompatibleApartmentFacets : Prop` is a structure with two fields.

- `injective : Function.Injective B.apartmentMap`. The apartment embeds into the building.
- `exists_isFacet_of_isFacet`: every facet `Y` of the building (published `B.IsFacet`) that
  meets `A(S)` is `B.apartmentMap '' Fa` for a facet `Fa` of the apartment for `Ψ` (published
  `AffineRootSystem.IsFacet B.affineRoots`).

Derived formulation. In KP the apartment `A` is a subset of `B(G)`, so the injectivity is
implicit in KP's statement. A facet of `B(G)` that meets `A` lies in `A`, because `A` is a
subcomplex. So the polysimplicial structure on `A` coming from `B` is the set of facets of `B`
that meet `A`. The published `B.IsFacet` defines the facets of the building as the
`G(F)`-translates of images of facets of `A` (Worker 1238's module). The images of facets of `A`
are facets of the building by the published `isFacet_image`. So the field
`exists_isFacet_of_isFacet` is the converse inclusion, and the two together say that the two sets
of facets of `A` agree. The face relations are then determined by the facets as subsets of `A`
(Notation 1.3.34). For the reduced building of a valuation, KP prove AS 6 in Proposition 7.6.3 (1).

Proved facts:

- `IsFacet.nonempty`: facets of the building are nonempty (from the published `mem_facet_self`).
- `HasCompatibleApartmentFacets.isFacet_image_iff`: under AS 6, for every `Fa ⊆ A`,
  `B.IsFacet (B.apartmentMap '' Fa) ↔ AffineRootSystem.IsFacet B.affineRoots Fa`.

## Not included

The corrected Definition 4.1.26 (corrections PDF p. 27) asks for Axioms 4.1.1, 4.1.2, 4.1.4,
4.1.6, 4.1.8, 4.1.9, 4.1.16, 4.1.17, 4.1.20 and 4.1.22. These parts are not stated here.

- Axiom 4.1.1, except the stabilizer clause: that `B(G)` is a building in the sense of
  Definition 1.5.5 with polysimplicial `G(k)`-action, and that a central isogeny `G → G′`
  induces an isomorphism `B(G) → B(G′)`. The second part concerns the construction `G ↦ B(G)`,
  not one `B`.
- AS 1 and the `m(u)` form of AS 2 (Axiom 4.1.6): they need the elements `m(u) = u′ u u″` of KP
  Proposition 2.11.17, which are not in the Library.
- Axiom 4.1.8 (2) and (3): they need `G(k)^0` and `Z(k)^0`, which are not in the Library.
- Axiom 4.1.9 (the Tits system `(G(k)^0_C, N(k) ∩ G(k)^0)` in `G(k)^0`) and Axiom 4.1.16 (the
  Iwahori decomposition, with `Z(k)^0` and the unipotent radicals `U^±`): they need `G(k)^0`,
  `Z(k)^0` and `U^±`, which are not in the Library.
- Axiom 4.1.17 (compatibility with isomorphisms `(k₁, G₁) → (k₂, G₂)`): it concerns the
  construction `G ↦ B(G)`, not one `B`.
- Axiom 4.1.20 (Bruhat–Tits group schemes `𝒢^1_Ω`) and Axiom 4.1.22 (structure of the reductive
  quotient): they need smooth affine `o`-models of `G`, which are not in the Library.
- No combined predicate for the corrected Definition 4.1.26 is defined.

## Sources

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:
  - Notation 2.6.15 (book PDF p. 133, printed p. 102);
  - Axioms 4.1.1 and 4.1.2 (book PDF pp. 188–189, printed pp. 157–158);
  - Axiom 4.1.4 (A 0)–(A 2) (book PDF pp. 189–190, printed pp. 158–159);
  - Axiom 4.1.6, AS 1–AS 6 (book PDF pp. 190–191, printed pp. 159–160);
  - Axiom 4.1.8 (book PDF p. 191, printed p. 160);
  - Definition 6.1.2, V 6 and V 7 (book PDF p. 230, printed p. 199);
  - Proposition 7.6.3, Remark 7.6.5, Fact 7.6.7, Proposition 7.6.8 and Corollary 7.6.9 (book PDF
    pp. 295–297, printed pp. 264–266).
- Kaletha–Prasad, *Corrections and additions* (1 November 2024), registered as
  `kaletha-prasad-2024-corrections`, SHA256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`:
  - PDF p. 27, the corrected Definition 4.1.26.
