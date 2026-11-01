# Etale restriction of constant-module associated sheaves

This module specializes the actual associated-sheaf comparison to module
representations by identifying restricted constant sheaves with constant
sheaves on the new base. It is an internal construction from
`EtaleAssociatedPullback` and `Langlands.Geometry.EtaleConstantPullback`.

## Parameters and conventions

Let `X` and `Z` be actual schemes in universe `u`, let `f : Z ⟶ X` be etale,
let `R : Type u` be a commutative ring, and let `G : Type u` be a group.
The module carriers also use universe `u`. The small etale sites have the
module-sheafification instances used by `etaleAssociatedFunctor`.

Let `Y : Action X.Etale G` be any actual etale cover object with a `G`-action,
and write `Yf = (etaleTorsorPullbackFunctor f G).obj Y`. This is the actual
scheme fiber-product base change with its induced deck action. There is no
finiteness, surjectivity, or torsor hypothesis. Such hypotheses enter local
triviality and exactness results, rather than the invariant sheaf construction
used here. All declarations are in `Langlands.Shimura.Coefficients`.

## Constant sheaf actions

`etaleConstantActionPullback f R` is the natural isomorphism

```
(constantSheaf X.smallEtaleTopology (ModuleCat R)).mapAction G
  ⋙ (EtalePullback.restriction f (ModuleCat R)).mapAction G
  ≅ (constantSheaf Z.smallEtaleTopology (ModuleCat R)).mapAction G.
```

It first identifies composition of the two mapped-action functors with the
mapped-action functor of their composite, and then applies
`Functor.mapActionCongr` to `EtalePullback.constantPullbackIso`. Thus it
intertwines every group operator and is natural in every equivariant module
map. The lemmas `etaleConstantActionPullback_hom_hom` and
`etaleConstantActionPullback_inv_hom` identify its forward and inverse
underlying sheaf maps with the corresponding constant-sheaf comparisons on
`M.V`.

## Actual associated sheaves

`etaleConstantAssociatedPullback f R Y` constructs

```
etaleAssociatedFunctor X Y ⋙ EtalePullback.restriction f (ModuleCat R)
  ≅ etaleAssociatedFunctor Z Yf.
```

For a module representation `M`, the source is the restriction of the actual
invariant subsheaf of the product-section sheaf for the constant sheaf of
`M`. The first step is `etaleAssociatedPullback`, whose target uses the
base-changed cover and the restricted original constant sheaf action. The
second step applies `associatedFunctor` for `Yf` to the constant-action
comparison constructed above. The target is consequently the actual
associated sheaf formed from `Yf` and the constant sheaf of the same module
representation on `Z`.

The result is a natural isomorphism on the full category
`Action (ModuleCat R) G`. It retains all equivariant coefficient maps and
therefore all diagrams of such representations at this fixed cover and
base. No constant-sheaf identification or associated-sheaf comparison is
assumed as input.

## Inclusion equations and their proofs

Let `cX(M)` and `cZ(M)` denote the constant sheaf actions, let `r` denote
restriction, let `p` be `etaleProductSheafPullback f R Y.V`, and let `k` be
`EtalePullback.constantPullbackIso f (ModuleCat R)` at `M.V`.
Write `iX` and `iZ` for the actual invariant inclusions of `cX(M)` and
`cZ(M)` and let `e` be the associated-sheaf comparison. Then
`etaleConstantAssociatedPullback_hom_inclusion` proves

```
e.hom ≫ iZ = r.map(iX) ≫ p.hom ≫ productSheaf(Z,Yf.V).map(k.hom).
```

`etaleConstantAssociatedPullback_inv_inclusion` proves

```
e.inv ≫ r.map(iX) = iZ ≫ productSheaf(Z,Yf.V).map(k.inv) ≫ p.inv.
```

These equations specify both maps on invariant sections. The order in the
inverse equation reverses the two comparisons used in the forward equation.
The forward proof expands the composite comparison, applies naturality of
`inclusion` to the constant-action map, and uses the forward inclusion
equation for `etaleAssociatedPullback`. The inverse proof uses the inverse
associated comparison's inclusion equation and inclusion naturality for the
inverse constant-action map. The underlying-map lemmas above and category
associativity finish both proofs.

## Provenance and remaining work

This construction is derived internally by composing the actual geometric,
sheafification, group-action, and invariant-limit comparisons in its imports.
It claims no additional theorem from the Harris literature. Compatibility
with changes of cover or group, iterated geometric base change of the whole
associated construction, arbitrary non-etale inverse image, actual Harris
coefficient-system realization, supports, traces, and cohomological
comparisons remain separate obligations.
