# Cross-cover coefficient maps and actual etale restriction

This file constructs isomorphisms of the actual cross-cover arrows under etale
base change. It proves the simultaneous cover, group and coefficient change
squares for arbitrary sheaf-valued coefficient actions and for constant module
representations. These are internal categorical consequences of the existing
geometric product and associated invariant-limit comparisons; no external
comparison theorem is assumed or transcribed.

## Objects, universes and hypotheses

All schemes, the commutative ring `R`, module carriers, and deck-group carriers
use universe `u`. Let `f : Z ⟶ X` be etale and write `T` for
`EtalePullback.restriction f (ModuleCat R)`. This is restriction by precomposition
with the actual small-etale site map, which composes structure morphisms with
`f`. Let `B = etaleObjectPullback f`, the actual scheme fiber-product functor
on small-etale objects. The action functor is
`etaleTorsorPullbackFunctor f G = B.mapAction G`.

Take groups `G,H`, a homomorphism `φ : H →* G`, cover actions
`Y : Action X.Etale G`, `Y' : Action X.Etale H`, and an equivariant cover map
`a : Y' ⟶ (Action.res X.Etale φ).obj Y`. A sheaf-valued coefficient map is
`c : F|H ⟶ E` for actions `F` of `G` and `E` of `H` on module sheaves over
`X`. The cover and coefficient maps after base change are exactly
`(B.mapAction H).map a` and `(T.mapAction H).map c`. These have the required
restricted-action sources definitionally: applying a functor commutes with
restriction along `φ` on carriers and all group operators.

Neither finiteness, surjectivity nor a torsor hypothesis is needed. Module
sheafification and the invariant-limit existence used in the imported
associated-sheaf constructions are supplied by the actual module-sheaf
instances. The coefficient module and both cover and coefficient actions are
arbitrary within the stated universe.

## The geometric cover square

For any morphism `b : V' ⟶ V` of small-etale objects over `X`,
`etaleProductSheafPullback_cover` proves

```text
T(coverPullback_X b F) ≫ productComparison(V', F)
  = productComparison(V, F) ≫ coverPullback_Z (B.map b) (T F).
```

Thus the previously constructed comparison of `F(V × U)` sheaves is natural
in unrestricted cover morphisms, extending the endomorphism/deck case. The
proof evaluates at an arbitrary small-etale test object `U` over `Z`, combines
the two contravariant presheaf maps, and uses the two-factor geometric
naturality `etaleProductPullbackHom_natural f b (identity U)`.

## Arbitrary sheaf-valued coefficients

Write `K_X(a,c)` for `crossCoverMap X.smallEtaleTopology φ a c` and `e_Y(F)`
for the hom component of `etaleAssociatedPullback f R Y` at `F`.
`etaleAssociatedPullback_crossCover` proves

```text
T(K_X(a,c)) ≫ e_Y'(E) = e_Y(F) ≫ K_Z(Ba,Tc).
```

The source is the restriction of the invariant sheaf associated to `Y,F`;
the target is the invariant sheaf associated to `BY',TE`. The proof applies
`hom_ext` for the target associated sheaf, so it suffices to compose with its
canonical invariant inclusion. The comparison-inclusion equation and
`crossCoverMap_inclusion` reduce this to product sheaves. Functoriality of
`T`, naturality of the product comparison in the coefficient sheaf, and the
geometric cover square above identify the composites.

`etaleCrossCoverPullbackIso` uses this proved square in `Arrow.isoMk`. It is
an isomorphism from `Arrow.mk (T.map K_X(a,c))` to
`Arrow.mk K_Z(Ba,Tc)`. Its source and target object isomorphisms are the
components of `etaleAssociatedPullback` for `Y,F` and `Y',E`, respectively.
The generated `_hom_left`, `_hom_right`, `_inv_left`, and `_inv_right`
equations expose these exact forward and inverse endpoint maps. Thus the
arrow comparison contains both endpoint identifications and their compatibility
with the cross-cover morphism.

## Constant module representations

For module actions `M` of `G`, `N` of `H` and `c : M|H ⟶ N`, the old and new
cross-cover arrows are the existing `etaleCrossCoverMap` on `X` and `Z`.
`etaleConstantAssociatedPullback_crossCover` proves

```text
T(etaleCrossCoverMap_X(φ,a,c)) ≫ constantComparison_Y'(N)
  = constantComparison_Y(M) ≫ etaleCrossCoverMap_Z(φ,Ba,c).
```

Here the coefficient representation and its map are retained; it is their
constant sheaves that are identified by `EtalePullback.constantPullbackIso`.
The proof again uses the target invariant inclusion. It applies the
constant-associated comparison-inclusion equation, the cross-cover inclusion
equation, product-comparison naturality and the cover square. Naturality of
`coverPullback` moves the constant-sheaf comparison past the pulled-back cover
map, and naturality of `constantPullbackIso` identifies the resulting
coefficient composites.

`etaleConstantCrossCoverPullbackIso` packages this square as an isomorphism
between the restricted old cross-cover arrow and the new cross-cover arrow.
Its endpoint isomorphisms are exactly `etaleConstantAssociatedPullback` at
`M` and `N`; the four generated endpoint equations expose their homs and
inverses.

## Scope

The result covers any compatible pair of cover and coefficient maps and any
group homomorphism, so it applies to the existing cover/group composition laws
without replacing those maps. It does not yet construct the comparison for a
whole varying-group transition cospan, prove coherence for successive geometric
base changes of the associated construction, or extend restriction to a
non-etale base morphism. The full Harris coefficient realization and its
cohomological comparisons remain separate construction obligations.
