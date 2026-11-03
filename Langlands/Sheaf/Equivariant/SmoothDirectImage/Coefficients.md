# Full smooth coefficient sheaves under spatial direct image

This internal construction lifts the actual ordinary-open locally constant
coefficient pullback through the smooth-direct-image universal property.
The source is the entire locally constant coefficient sheaf of a smooth
representation, with its already proved local smoothness. No subsheaf is
substituted for this source.

## Scope

The commutative coefficient ring `R`, topological group `G`, spaces `X`, `Y`,
`Z` and module carriers share universe `u`. The spaces have `G`-actions with
continuous individual translations and `HasStableNeighbourhoods`: every open
neighborhood contains an open neighborhood stable under an open subgroup.
A spatial map `f : C(X, Y)` is supplied with its equivariance equation `hf`.
Every coefficient object is an arbitrary `SmoothRep R G`, and all its
intertwiners are retained. No coefficient-module topology, properness or
exactness assumption is used.

Write `L_X` for `LocallyConstantSheaf.smoothFunctor R G X` and `D_f` for
`SmoothDirectImage.functor f hf`. The underlying ordinary sheaf of `L_X(M)`
is the full sheaf of locally constant functions with values in `M`.
The target `D_f(L_X(M))` consists of the locally smooth sections of its
ordinary direct image, using the existing smooth coreflector on `Y`.

## Actual maps and coefficient naturality

`coefficientMap f hf M` has type

```text
L_Y(M) ⟶ D_f(L_X(M)).
```

Its definition applies `SmoothDirectImage.lift` to the existing ordinary
`DirectImage.coefficientMap f hf M.representation`. That original map
precomposes a locally constant section with `f` on its inverse-image open.
The source `L_Y(M)` is smooth by `LocallyConstantSmooth`, so the established
universal property supplies its factorization through the smooth target.
There is no assumption that ordinary direct image preserves all smooth sheaves.

`coefficientMap_inclusion` proves that forgetting smoothness and composing
with the actual smooth-image inclusion gives precisely the original map.
For an action-open `U` in `Y`, a section `s` of `L_Y(M)` over `U`, and a point
`x` of its inverse-image open, `coefficientMap_apply` identifies the value
of the underlying resulting section with
`s (DirectImage.pointMap f hf U x)`.

`coefficientNatTrans` assembles these maps as a natural transformation
`L_Y ⟶ L_X ⋙ D_f`. Its naturality proof compares the actual sheaf maps on
each section; subtype extensionality removes the local-smoothness witness,
and the resulting equality is reflexivity. `coefficientMap_naturality`
records this square for every original smooth coefficient intertwiner.

## Identity, composition and provenance

`coefficientMap_id` identifies the coefficient map for the identity spatial
map with the component of the actual `SmoothDirectImage.idIso` unit.
For `f : X → Y` and `g : Y → Z`, `coefficientMap_comp` proves

```text
b_(g ∘ f)(M) =
  b_g(M) ≫ D_g.map(b_f(M)) ≫ compMap(f, g).app(L_X(M)),
```

where `b_f` denotes `coefficientMap f hf`. Both proofs use
`SmoothDirectImage.hom_ext` to test equality in the full ordinary direct
image and then apply the existing ordinary coefficient identity or
composition equation. The composition comparison is the constructed lax
map; no inverse is asserted.

The provenance is internal: the module combines the actual full locally
constant smooth sheaf functor, ordinary coefficient pullback, and the smooth
direct-image adjunction and coherence maps. It introduces no external
literature assertion. Higher chain and cohomology maps, their analytic or
étale realization, resolution exactness, acyclicity, derived comparison,
arithmetic coefficients and Harris specialization remain separate obligations.
