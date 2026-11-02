# Spatial maps on coinduced stalk families

This module constructs the spatial comparison for the actual right Kan
coinduction of ordinary stalk families. It uses the natural indexed-family
coordinates from [Functoriality](Functoriality.md) and the actual
neighborhood-colimit maps from [Godement/SpatialZero](../Godement/SpatialZero.md).

## Scope and provenance

Fix one universe `u`, a commutative ring `R : Type u`, a group `G : Type u`,
and topological `G` spaces `X`, `Y`, and `Z` in `Type u`. The coinduced
comparisons require `ContinuousConstSMul` on the relevant spaces, meaning
that each fixed group translation is continuous. The spatial input is an
actual continuous map `f : C(X,Y)` with equivariance
`hf : ∀ g x, f (g • x) = g • f x`.

All sheaves are `TopologicalSheaf G X (ModuleCat.{u} R)` and their analogues
on `Y` and `Z`: transport presheaves whose restriction to ordinary open
inclusions is a sheaf. `f_*` denotes the actual full direct-image functor
`DirectImage.sheaf f hf`, which precomposes with inverse images of opens and
retains every group label. Every stalk is an actual underlying ordinary
presheaf stalk. No topology on `G`, stable-neighbourhood condition, smoothness
or properness is assumed.

This is an internal construction derived from those imported sheaf,
coinduction, indexed-family and spatial-stalk constructions. It does not
claim an independent external theorem. The existing coinduced functor and
its coordinate isomorphism are imported unchanged.

## The indexed-family spatial map

Write `T_X(F) = familyFunctor.obj F`. Its sections over `U` are entries
`s(g,x) ∈ F_x` indexed by `g ∈ G` and `x ∈ X` with `g • x ∈ U`.
`familySpatialMap f hf F` has type

```
T_Y(f_*F) ⟶ f_*T_X(F).
```

Over an open `U` of `Y`, its `(g,x)` entry for `f(g • x) ∈ U` is

```
(familySpatialMap(s))(g,x) = stalkMap(f,F,x)(s(g,f(x))).
```

Equivariance supplies `g • f(x) ∈ U`. Here `stalkMap(f,F,x)` is the actual
map `(f_*F)_{f(x)} ⟶ F_x` induced by inverse images of neighborhoods. Thus the
construction uses the original input entries and their actual stalk maps;
it does not take a spatial comparison as a field or hypothesis.

Linearity follows from linearity of this stalk map. Every transport arrow
multiplies the group index on the left, leaving the stalk point unchanged,
so the section map is natural in all labelled arrows. The formula is
`familySpatialMap_apply`. Naturality in every original sheaf morphism follows
from `Godement.Spatial.stalkMap_naturality` and gives
`familySpatialNatTrans : f_* ⋙ T_Y ⟶ T_X ⋙ f_*`.

`familySpatialMap_id` and `familySpatialMap_comp` follow from the actual
identity and composition laws for the neighborhood-colimit stalk maps. In
the composition law, the direct image along `g.comp f` is definitionally
the composite direct image, as in `DirectImage.compIso`. The pointwise
family formulas and these two laws themselves do not require continuity
of group translations.

## The actual right Kan coinduction

Write `Q_X = coinducedZeroFunctor`. Its object on `F` is right Kan
coinduction of the ordinary sheaf of unrestricted stalk families.
`coinducedZeroNatIso : Q_X ≅ T_X` is the existing natural coordinate
isomorphism. `coinducedSpatialNatTrans` is the composite

```
Q_Y(f_*F) → T_Y(f_*F) → f_*T_X(F) → f_*Q_X(F).
```

The first arrow is the coordinate isomorphism on `f_*F`; the middle one is
the constructed indexed-family spatial map; the last is direct image of
the inverse coordinate isomorphism. `coinducedSpatialMap` abbreviates a
component. `read_coinducedSpatialMap` proves that reading the resulting Kan
section gives precisely the spatial stalk map in each `(g,x)` coordinate.
The inverse-coordinate identity proves this formula.

`coinducedSpatialMap_id` and `coinducedSpatialMap_comp` prove the identity
and composition laws on the actual Kan sections. Their proofs use
injectivity of the existing `read` equivalence and the pointwise formula,
then the corresponding stalk-map laws.

## Coaugmentation compatibility

`familyCoaugmentation` is `coinducedCoaugmentation` followed by the existing
natural coordinate isomorphism. For a section `s` of `F` on `U`,
`read_coinducedCoaugmentation_stalkPull` expresses its coordinate as

```
(g,x) ↦ stalkPull(F,g,x,g • x)(germ at g • x of s).
```

Here `stalkPull` is actual group transport on neighborhood-colimit stalks.
The equality follows from the previously proved transported-section germ
formula and `germ_stalkPull_arrow` at `coordinateArrow U g`.

`coaugmentation_familySpatialMap` proves

```
familyCoaugmentation(f_*F) ≫ familySpatialMap(f,F)
  = f_*(familyCoaugmentation(F)).
```

The proof uses the group-transport expression above. Actual spatial stalk
maps commute with actual group stalk transport, including the equality
`g • f(x) = f(g • x)`. The identity `germ_stalkMap` then identifies the
spatial image of the germ with the germ on the inverse-image open.

Finally `coaugmentation_coinducedSpatialMap` proves the corresponding
identity for `coinducedCoaugmentation` and `coinducedSpatialMap`. It cancels
direct image of the coordinate isomorphism and uses its inverse identity.
All coaugmentation maps are the constructed maps from the imported
adjunction and germ functors.

## Retained boundaries

The module supplies degree-zero spatial maps and their intrinsic laws. It
does not compare them with the separate smooth Godement functor, construct
higher smooth spatial maps, prove exactness or acyclicity, or identify any
Godement cohomology with a derived functor. Analytic, etale, arithmetic,
Galois and Shimura specializations remain separate constructions.
