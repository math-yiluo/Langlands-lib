# Passing to the relative identity component keeps closed split tori

Lean module: `Langlands.GroupScheme.IntegralModel.SpecialTorusNeutralModel`.

Author: Worker 88, for Task 5707 (`f502c3c7-c095-4c74-bf82-ad8ffb916f57`). Submitted by
Worker 25 for Task 5970 (`5e417cd1-e617-4ae4-adf8-da82b98ba654`).

This module reduces the four conjuncts of the target
`Langlands.Geometry.Building.SpecialTorusIntegralModelStatement` to a weaker input. The
input is a smooth model without the connected special fibre, containing the two closed
split tori. The module does not prove the target. It does not use
`SpecialTorusExistenceStatement`, `UnramifiedSpecialApartmentStatement` or
`ValuationApartmentAxiomsExistenceStatement`, and it does not import their modules.

## Model homomorphisms and generic torus maps

Let `R` be a domain with fraction field `K`. Let `M : IntegralModel R K G`,
`N : IntegralModel R K H` and `φ : M.Hom N f` over `f : G ⟶ H`.

* `Hom.genericTorusMap_comp`: for a commutative group scheme `T` over `R` and
  `j : T ⟶ M.group`, `N.genericTorusMap T (j ≫ φ.hom) = M.genericTorusMap T j ≫ f`. This
  unfolds `genericTorusMap` (generic fibre of the map, then the model's `genericIso`) and
  applies the compatibility square `φ.generic_comm`.
* `Hom.genericTorusMap_comp_of_id`: the case `f = 𝟙 G`.
* `Hom.baseChangeCoefficients φ A L`: under the hypotheses of the Library's `IntegralModel.baseChange`,
  `φ` gives a model homomorphism `(M.baseChange A L).Hom (N.baseChange A L)` over the base
  change of `f`. The underlying map is the base change of `φ.hom` (`Hom.baseChangeCoefficients_hom`).
  The compatibility square is the Library's `baseChangeGenericIso_naturality`.

For a nonarchimedean local field `F`, `Hom.baseChangeUnramified_genericTorusMap_comp` is the
corresponding statement for `baseChangeUnramified`, for a homomorphism over `𝟙 G`. It uses
the same algebra and scalar-tower instances as the definition of `baseChangeUnramified`. The
base change of `𝟙 G` is the identity (`Functor.map_id`).

## Main theorem

`exists_connected_specialTorusModel`. Let `F` be a nonarchimedean local field and `G` a
connected reductive `F`-group. Let `S` be a commutative `F`-group scheme with
`iS : S ⟶ G`, and let `M : IntegralModel 𝒪[F] F G` be smooth. Assume:

* (torus over `𝒪[F]`) there are a commutative `𝒪[F]`-group scheme `𝒮`, a map
  `j : 𝒮 ⟶ M.group` and an isomorphism `e` from the generic fibre of `𝒮` to `S`, such that
  `𝒮` is a split torus, `j` is a closed subgroup and
  `M.genericTorusMap 𝒮 j = groupHom e.hom ≫ iS`;
* (torus over `O_K`) there are a commutative `O_K`-group scheme `𝒜` and a map
  `a : 𝒜 ⟶ M.baseChangeUnramified.group`, such that `𝒜` is a split torus, `a` is a closed
  subgroup and `M.baseChangeUnramified.genericTorusMap 𝒜 a` is a maximal split torus.

Then there is an `N : IntegralModel 𝒪[F] F G` satisfying the four conjuncts of the target
for the same `G`, `S` and `iS`. That is, `N` is smooth, its special fibre over `𝓀[F]` has
connected total space, and it satisfies the two torus conditions above in place of `M`.
`IsMaximalSplitTorus iS` is not needed for this step.

Proof.

1. `G.X.hom` is geometrically connected by the Library's
   `geometricallyConnected_of_connected`. The instances it needs come from
   `IsConnectedReductive`: smoothness gives locally finite type, affineness gives
   quasi-compactness, and connectedness of `G.X.left` is part of the structure.
2. `smoothExistence` gives a smooth relative identity component `i : H ⟶ M.group` with
   `H.X.hom` geometrically connected. Set `N := M.neutralModel hM hi hH` (module
   `RelativeComponentConstruction`), with inclusion `φ := M.neutralInclusion hM hi hH`.
3. `N` is smooth by `hH`. Its special fibre is connected by
   `connectedSpace_baseChange_of_geometricallyConnected`.
4. Split tori are reductive (`IsSplitTorus.isReductive`) and so geometrically connected
   (`IsReductive.geometricallyConnected`). By `exists_hom_lift`, `j = y ≫ i` for a
   homomorphism `y : 𝒮 ⟶ H`. Then `y` is a closed subgroup by `isClosedSubgroup_of_comp`,
   and `N.genericTorusMap 𝒮 y = M.genericTorusMap 𝒮 j` by `Hom.genericTorusMap_comp_of_id`.
5. By `smoothBaseChange`, the base change of `i` to `O_K` is a relative identity component
   of `M.baseChangeUnramified.group`. Lift `a` through it as in step 4 to get `y`. Then
   `Hom.baseChangeUnramified_genericTorusMap_comp` gives
   `N.baseChangeUnramified.genericTorusMap 𝒜 y = M.baseChangeUnramified.genericTorusMap 𝒜 a`,
   so this map is a maximal split torus.

## Use and source route

`Langlands.Geometry.Building.SpecialTorusIntegralModelReduction` applies
`exists_connected_specialTorusModel` to a smooth model supplied by the residual
`Langlands.Geometry.Building.SpecialTorusBoundedModelStatement`, after producing the two
closed split tori with `Langlands.GroupScheme.IntegralModel.SplitTorusBoundedPoints`.

In Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), the model with connected
special fibre is `𝒢^0_x`, the relative identity component of `𝒢^1_x` (Definition 4.1.18,
Axiom 4.1.20 and §9.2.5; printed pp.162–163 and 327–328 / PDF pp.193–194 and 358–359).
This module obtains it from the Library's smooth relative identity component instead of
from a building.

The coefficient-square homomorphism and its underlying-map formula are imported from
`Langlands.GroupScheme.IntegralModel.BaseChangeCoefficientHom`; the model argument
uses that shared definition.
