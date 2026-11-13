# Valuation-building quotients compared along a group homomorphism

Module `Langlands.Geometry.Building.ValuationBuildingQuotientMap`.

The Library's reduced building of an apartment class `D` is the quotient
`ApartmentQuotient D.sharpFixerFamily` of `G(k) × A` (KP (7.6.2), Remark
7.6.5). It identifies `(g, x) ∼ (h, y)` when some `n ∈ N(k)` has `n x = y` and
`g⁻¹ h n ∈ G(k)^♯_x`. This module compares two such quotients along a group
homomorphism. It packages the needed data for apartment classes as
`KPApartmentData.Comparison` and `KPApartmentData.Transfer`, and shows that a
transfer gives an equivariant isomorphism of buildings.

## Quotient maps

Namespace `ApartmentQuotient`, section `HomMap`. Let `H₁` and `H₂` be groups
with subgroups `N₁` and `N₂` acting on sets `A₁` and `A₂`, and let
`P₁`, `P₂` be covariant subgroup families. Take `θ : H₁ →* H₂` and a bijection
`ε : A₁ ≃ A₂`.

- `IsHomComparison P₁ P₂ θ ε` (a `Prop` structure) asserts:
  - `θ(N₁) ⊆ N₂` (`map_mem`);
  - `ε(n x) = θ(n) ε(x)` (`map_smul`);
  - `(P₁ x).map θ = P₂ (ε x)` (`map_family`);
  - `θ g ∈ N₂ → g ∈ N₁` (`mem_of_map_mem`);
  - every `h ∈ H₂` is `θ(g) · n` with `n ∈ N₂` (`exists_mul`).
- `homMap hc` is the map `[(g, x)] ↦ [(θ g, ε x)]`, well defined by
  `IsHomComparison.apartmentRel`. `homMap_mk`, `homMap_apartment` and
  `homMap_smul` give its values and its `θ`-equivariance.
- `homMap_injective`: if `[(θ g, ε x)] = [(θ h, ε y)]`, choose `n'` and write
  the fixer element as `θ p` with `p ∈ P₁ x` (`map_family`). Then
  `θ(h⁻¹ g p) = n'`, so `h⁻¹ g p ∈ N₁` (`mem_of_map_mem`), and
  `h⁻¹ g p` witnesses `(g, x) ∼ (h, y)`.
- `homMap_surjective`: write `h = θ(g) n` (`exists_mul`). Then
  `[(h, y)] = [(θ g, n y)]`, which is the image of `[(g, ε⁻¹(n y))]`.
- `homEquiv hc` is the resulting bijection (`homEquiv_apply`).

## Affine roots

Namespace `AffineRootSystem`:

- `transportedRoots_trans`: transport along a composite affine equivalence is
  the composite of the transports.
- `transportedRoots_eq_of_mem_rootStabilizer_algebraic`: an affine automorphism in the
  stabilizer of a root set transports the set to itself, under algebraic
  additive-torsor hypotheses. This name distinguishes it from the existing
  normed-space version in `BuildingFacetCentroids`; both statements retain
  their original hypotheses.

## Comparisons and transfers of apartment classes

Namespace `KPApartmentData`. Let `D₁` and `D₂` be apartment classes for
`(G₁, S₁)` and `(G₂, S₂)` over a field `k`, and take
`θ : G₁(k) →* G₂(k)`.

- `Comparison D₁ D₂ θ` (a structure) consists of an affine equivalence
  `e : D₁.Apartment ≃ᵃ[ℝ] D₂.Apartment` with:
  - `θ(N₁(k)) ⊆ N₂(k)` (`map_mem_normalizerPoints`);
  - `e(n x) = θ(n) e(x)` (`e_smul`);
  - `(D₁.sharpFixer {x}).map θ = D₂.sharpFixer {e x}` (`map_sharpFixer`);
  - `transportedRoots e D₁.affineRoots = D₂.affineRoots`
    (`transportedRoots_eq`).
- `Transfer D₁ D₂ θ` extends `Comparison` by
  `mem_normalizerPoints_of_map` (`θ g ∈ N₂(k) → g ∈ N₁(k)`) and `exists_mul`
  (`G₂(k) = θ(G₁(k)) · N₂(k)`).
- `Comparison` operations:
  - `refl` and `trans` (composition along `θ'.comp θ`, with `trans_e`);
  - `congrHom` replaces `θ` by an equal homomorphism (`congrHom_e`);
  - `congrLeft` replaces `D₁` by an equal class, without changing the
    linear part (`congrLeft_linear`);
  - `e_symm_smul`: the equivariance of `e.symm`.
- `Transfer` operations:
  - `refl`, `trans` and `trans_e`;
  - `isHomComparison`: the sharp-fixer families satisfy `IsHomComparison`
    for `θ` and `e`;
  - `reducedBuildingEquiv t : D₁.ReducedBuilding ≃ D₂.ReducedBuilding`, the
    map `[(g, x)] ↦ [(θ g, e x)]`;
  - `reducedBuildingEquiv_mk`, `reducedBuildingEquiv_apartmentMap` and
    `reducedBuildingEquiv_smul` (`θ`-equivariance).

## The building isomorphism

Namespace `ValuationBuildingData`, for valuation-building data `B₁`, `B₂` and
`t : B₁.apartment.Transfer B₂.apartment θ`:

- `isFacet_normalizer_image_iff`: normalizer elements permute the facets of
  the apartment. They act by affine automorphisms in the stabilizer of the
  affine roots (`normalizerAffineEquiv_mem_rootStabilizer`).
- Namespace `TransferIso` has four results:
  - `translatedApartmentMap`: `reducedBuildingEquiv` maps the translated chart
    `g · A(B₁)` to `θ(g) · A(B₂)` through `e`;
  - `image_translatedApartmentMap` and `image_apartment`: the corresponding
    statements for images of sets and for whole apartments;
  - `isApartment_image_iff`: apartments correspond, using `exists_mul` and
    the fact that `N₂` stabilizes the standard apartment;
  - `isFacet_image_iff`: facets correspond, using the root correspondence
    and `isFacet_normalizer_image_iff` for the normalizer factor of
    `exists_mul`.
- `Transfer.isEquivariantBuildingIso t` proves
  `IsEquivariantBuildingIso B₁ B₂ θ t.reducedBuildingEquiv`. The building
  isomorphism has the two image criteria above and the affine charts
  `exists_affineEquiv g := ⟨θ g, e, …⟩`. Equivariance is
  `reducedBuildingEquiv_smul`.
- `exists_isEquivariantBuildingIso_of_transfer` is the existential form.

## Provenance

This is internal. It compares the quotients of KP (7.6.2) (Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), §7.6, printed p.264, and Remark
7.6.5, printed p.266) along a homomorphism of groups. KP compare buildings of
`G_sc`, `G_der`, `G` and `G_ad` via Tits systems (Lemma 1.4.13, (7.6.1)).
The hypotheses of a transfer correspond to the conditions that make the
induced map of quotients well defined, injective and surjective.
