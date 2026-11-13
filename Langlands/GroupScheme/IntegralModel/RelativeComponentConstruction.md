# The relative identity component of a smooth integral model

Lean module: `Langlands.GroupScheme.IntegralModel.RelativeComponentConstruction`.

Author: Worker 88, for Task 5707 (`f502c3c7-c095-4c74-bf82-ad8ffb916f57`). Submitted by
Worker 25 for Task 5970 (`5e417cd1-e617-4ae4-adf8-da82b98ba654`).

This module takes an existing smooth integral model over a discrete valuation ring and
replaces it by its relative identity component. In Kaletha–Prasad this is the passage from
the smooth model `G_x` to the connected model `G^0_x`. The module only uses Library results
about represented relative identity components:

* `RelativeIdentityComponent.smoothExistence`,
* `RelativeIdentityComponent.smoothBaseChange`,
* `RelativeIdentityComponent.smoothDvrAffineness`,
* `RelativeIdentityComponent.inRelativeIdentityComponent_of_geometricallyConnected`.

It introduces no new statement. Every declaration is a definition or a theorem.

## Relative identity components (namespace `IsRelativeIdentityComponent`)

Fix a base scheme `S`, a group scheme `G` over `S` and `i : H ⟶ G` with
`hi : IsRelativeIdentityComponent G i`.

* `mono_hom`: the underlying morphism of `i` over `S` is a monomorphism. It is an open
  immersion by `hi.isOpenImmersion`.
* `exists_lift_of_geometricallyConnected`: let `T` be over `S` with geometrically connected
  structure morphism. Let `x : T ⟶ G.X` and `a : 𝟙_ ⟶ T` with `a ≫ x` equal to the unit of
  `G`. Then `x` factors through `H.X`. This is `hi.factors_iff` together with the Library
  lemma that such points lie in the relative identity component.
* `exists_hom_lift`: every group homomorphism `j : T ⟶ G` from a group scheme `T` with
  geometrically connected structure morphism factors as `y ≫ i` for a group homomorphism
  `y : T ⟶ H`. Proof: lift the underlying morphism using the unit section of `T`. The
  lift is compatible with the unit and the multiplication because `i` is a monomorphism and
  `i` and `j` are both homomorphisms.
* `isClosedSubgroup_of_comp`: if `y ≫ i` is a closed subgroup, then so is `y`. Here
  `IsClosedSubgroup` means that the underlying scheme morphism is a closed immersion. The
  open immersion `i` is separated, so Mathlib's `IsClosedImmersion.of_comp` applies.
* `isIso_hom_of_geometricallyConnected`: if `G.X.hom` is geometrically connected, then the
  underlying morphism of `i` is an isomorphism. Lift the identity of `G.X` through `i` and
  cancel the monomorphism `i`.
* `isoOfGeometricallyConnected`: the resulting isomorphism `H ≅ G` of group schemes, built
  with `Grp.mkIso`. Its forward map is `i` (`isoOfGeometricallyConnected_hom`).

`connectedSpace_baseChange_of_geometricallyConnected`: if `H.X.hom` is geometrically
connected, then for every field `k` and every `b : Spec k ⟶ S` the total space of the base
change of `H` along `b` is connected. Geometric connectedness is stable under base change,
and over a field Mathlib's `GeometricallyConnected.connectedSpace_of_subsingleton` applies.

## Integral models (namespace `IntegralModel`)

Let `R` be a domain with fraction field `K`, and let `M : IntegralModel R K G`.

* `geometricallyConnected_genericFibre`: if `G.X.hom` is geometrically connected, then so is
  the structure morphism of the actual generic fibre of `M`. The model's `genericIso` gives
  a pullback square along an isomorphism, so the property transfers.

Now let `R` be a discrete valuation ring, `M` smooth (`hM : M.IsSmooth`), `G.X.hom`
geometrically connected, and `i : H ⟶ M.group` a relative identity component (`hi`) with
`hH : Smooth H.X.hom`.

* `neutralGenericIso hM hi`: an isomorphism from the generic fibre of `H` to the generic
  fibre of `M`. By `smoothBaseChange`, the generic fibre of `i` is a relative identity
  component of the generic fibre of `M`. That generic fibre is geometrically connected, so
  `isoOfGeometricallyConnected` applies. Its forward map is the generic fibre of `i`
  (`neutralGenericIso_hom`).
* `neutralModel hM hi hH : IntegralModel R K G`: the model with group `H`. It is affine by
  `smoothDvrAffineness`, which uses that `M` is affine. Flatness and finite type follow
  from smoothness. Its generic identification is `neutralGenericIso` followed by
  `M.genericIso`. It is smooth (`neutralModel_isSmooth`), and its group is `H`
  (`neutralModel_group`).
* `neutralInclusion hM hi hH : (M.neutralModel hM hi hH).Hom M (𝟙 G)`: the model
  homomorphism with underlying map `i` (`neutralInclusion_hom`). Its generic compatibility
  square is `neutralGenericIso_hom`.
* `relativeComponentModelData hM hi hH hgc`: packages `M`, the neutral model and the
  inclusion as the Library's `BruhatTits.IntegralModels.RelativeComponentModelData`, given
  `hgc : GeometricallyConnected H.X.hom`. Connected fibres come from the Library's
  `hasConnectedFibres_of_geometricallyConnected`.
* `exists_relativeComponentModelData hM`: every smooth model over a discrete valuation ring
  of a group with geometrically connected structure morphism is the `full` model of some
  relative-component model data whose neutral group has geometrically connected structure
  morphism. The data comes from `smoothExistence`.

## Source route

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, define the relative identity component
`𝒢^0` of a smooth `o`-group scheme `𝒢` as its largest subgroup scheme with connected fibres
(Definition 4.1.18, printed p.162 / PDF p.193). They cite SGA 3, Exp. VI_B, Theorem 3.10
for its existence as an open subscheme, and note that it is affine when `𝒢` is. Axiom
4.1.20 (printed p.163 / PDF p.194) and §9.2.5 (printed pp.327–328 / PDF pp.358–359) take
`𝒢^0_x` to be the relative identity component of `𝒢^1_x`. The Library already contains the
represented relative identity component and these properties, and this module only
assembles them for `IntegralModel`.
