# Chart isomorphisms of reduced buildings

This is an internal coherence unit toward Kaletha–Prasad Axiom 4.1.17
(compatibility with isomorphisms) for the valuation-quotient buildings of
supplied `ValuationBuildingData`. It does not prove that axiom. It isolates the
bookkeeping that turns a map given in apartment coordinates into an equivariant
isomorphism of buildings in the sense of `ValuationBuildingData.IsEquivariantBuildingIso`.

## Provenance

The source motivation is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Axiom 4.1.17, printed p.162 (PDF p.193), and the construction of the
reduced building as the quotient of `G(F) × A` by relation (4.4.2)
(Proposition 4.4.4, printed p.183),
read with the authors' corrections of 1 November 2024 (PDF p.27). Registered
source IDs: `kaletha-prasad-2023-bruhat-tits-new-approach`,
`kaletha-prasad-2024-corrections`. The declarations below are derived from the
published `ApartmentQuotient`, `KPApartmentData` and `ValuationBuildingData`
API; they are not statements from the source.

## Quotient congruence

For groups `H₁`, `H₂` with subgroups `N₁`, `N₂`, an `N₁`-set `A₁` and an
`N₂`-set `A₂`, let `θ : H₁ ≃* H₂` be a group isomorphism with
`θ g ∈ N₂ ↔ g ∈ N₁` (hypothesis `hN`), and `e : A₁ ≃ A₂` an equivalence with
`e (n • x) = θ(n) • e x` (hypothesis `he`, where `congrNormalizer θ hN n` is
`θ n` viewed in `N₂`). If the subgroup families satisfy
`θ g ∈ P₂ (e x) ↔ g ∈ P₁ x` (hypothesis `hP`), then

- `ApartmentQuotient.apartmentRel_congr_iff`: `(g, x) ~ (h, y)` for
  `apartmentRel N₁ P₁` if and only if `(θ g, e x) ~ (θ h, e y)` for
  `apartmentRel N₂ P₂`. The forward direction maps the witness `n` to
  `θ n`; the reverse direction pulls the witness back along `θ.symm`.
- `ApartmentQuotient.congrEquiv` is the resulting `Quotient.congr` of
  `θ × e`, and `congrEquiv_mk` records `[(g, x)] ↦ [(θ g, e x)]` (by `rfl`).

## Chart isomorphisms

`KPApartmentData.IsChartIso D₁ D₂ θ c e Φ` is a structure on
`Φ : D₁.ReducedBuilding ≃ D₂.ReducedBuilding`, for apartment data possibly
over different fields `k₁`, `k₂` (in one universe), a monoid homomorphism
`θ : G₁(k₁) →* G₂(k₂)`, a point `c ∈ G₂(k₂)` and an affine equivalence
`e : D₁.Apartment ≃ᵃ[ℝ] D₂.Apartment`. Its two fields are

- `map_smul_apartmentMap`: `Φ (g • D₁.apartmentMap x) = (θ g * c) • D₂.apartmentMap (e x)`;
- `transportedRoots_eq`: `AffineRootSystem.transportedRoots e D₁.affineRoots = D₂.affineRoots`.

Lemmas:

- `transportedRoots_refl` and `transportedRoots_trans`: transport of affine
  functionals along the identity is the identity, and along a composite is the
  composite (`Set.image_image`).
- `IsChartIso.refl`: the identity with `θ = id`, `c = 1`, `e = id`.
- `IsChartIso.trans`: chart isomorphisms compose, with group map `θ₂ ∘ θ₁`,
  base point `θ₂ c₁ * c₂` and affine map `e₁.trans e₂`.
- `IsChartIso.smul`: left translation `MulAction.toPerm c` by `c ∈ G(k)` is a
  chart isomorphism along conjugation by `c`, with base point `c` and `e = id`,
  since `c g x = (c g c⁻¹) c x`.
- `congrBuildingEquiv D₁ D₂ θ e hN he hP` is `ApartmentQuotient.congrEquiv`
  for the sharp-fixer families, for `θ : G₁(k₁) ≃* G₂(k₂)` matching the actual
  normalizers `normalizerPoints i₁`, `normalizerPoints i₂`, an affine
  equivalence `e` intertwining the normalizer actions, and matching sharp
  fixers `θ g ∈ D₂.sharpFixer {e x} ↔ g ∈ D₁.sharpFixer {x}`.
  `congrBuildingEquiv_mk` is its formula on representatives.
- `isChartIso_congrBuildingEquiv`: if moreover `e` transports the affine roots
  onto the affine roots, this equivalence is a chart isomorphism along
  `θ.toMonoidHom` with base point `1`. The proof unfolds `apartmentMap x` as the
  class of `(1, x)` and uses `ApartmentQuotient.smul_mk`.

## From charts to equivariant building isomorphisms

For `B₁ : ValuationBuildingData G₁` over `F₁` and `B₂ : ValuationBuildingData G₂`
over `F₂` (nonarchimedean local fields, possibly different):

- `image_translatedApartmentMap_of_isChartIso`: `Φ` maps the translated facet
  image `{g • B₁.apartmentMap x | x ∈ Fa}` onto
  `{(θ g * c) • B₂.apartmentMap x | x ∈ e '' Fa}`.
- `image_apartmentImage_of_isChartIso`: `Φ (g • B₁.apartmentImage) = (θ g * c) • B₂.apartmentImage`,
  using the published `range_translatedApartmentMap` and surjectivity of `e`.
- `isEquivariantBuildingIso_of_isChartIso`: if `θ` is surjective, a chart
  isomorphism `Φ` satisfies `ValuationBuildingData.IsEquivariantBuildingIso B₁ B₂ θ Φ`.
  Facets: forward images use `isFacet_image_iff_of_transportedRoots_eq`; for
  the reverse direction a facet `g₂ • Fa₂` of `B₂` is the image of
  `g₁ • e⁻¹(Fa₂)` where `θ g₁ = g₂ c⁻¹` (surjectivity), and `Φ` is injective.
  Apartments are handled the same way with `image_apartmentImage_of_isChartIso`.
  The local chart condition takes the apartment map `e` and translation
  `θ g₁ * c`. Equivariance `Φ (g • y) = θ g • Φ y` follows by writing
  `y = g' • B₁.apartmentMap x` (`exists_smul_apartmentMap`) and applying the
  chart formula twice.

No building axiom, V 7, AS 5 or availability hypothesis is used.
