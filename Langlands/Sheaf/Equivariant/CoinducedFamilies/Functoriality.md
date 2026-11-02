# Functorial coordinates for coinduced stalk families

This module makes the existing coordinates of coinduced stalk families natural
in the original equivariant sheaf, and identifies the actual coaugmentation in
those coordinates. It extends
[`CoinducedFamilies`](../CoinducedFamilies.md) and its
[`Coordinates`](Coordinates.md) without changing either construction.

## Scope and provenance

Fix one universe `u`, a commutative ring `R : Type u`, a group `G : Type u`,
and a topological space `X : Type u` with a `G` action. For the Kan-extension
comparisons require `ContinuousConstSMul G X`: translation by each fixed group
element is continuous. No topology on `G`, smoothness condition, stable
neighbourhood condition, or properness assumption is used.

The category is `TopologicalSheaf G X (ModuleCat.{u} R)`, consisting of
transport presheaves whose restriction to ordinary open inclusions is a sheaf.
All stalks are those of the genuine underlying ordinary presheaf. The
construction is internal: its provenance is the actual indexed-family,
ordinary germ, coinduction and adjunction constructions in the imported
Library modules. It makes no independent attribution to an external theorem.

For an equivariant sheaf `F`, write `F_y` for its underlying stalk at `y`.
Over a transport open `U`, the existing family sheaf has sections

```
s(g,y) ∈ F_y,    g ∈ G, y ∈ X, g • y ∈ U.
```

The existing `coinducedZero F` is the right Kan coinduction of
`ordinaryZero F`, the ordinary sheaf of unrestricted stalk families. Its
coordinate isomorphism `coinducedZeroIso F` was already constructed from an
actual limit universal property. This module retains that same isomorphism.

## Functorial stalk coordinates

For a morphism `a : F ⟶ F'`, `familyMap a` applies the induced stalk map
`a_y : F_y ⟶ F'_y` in each coordinate:

```
(familyMap a)(s)(g,y) = a_y(s(g,y)).
```

It is linear and natural for every labelled transport arrow. Such an arrow
multiplies the group coordinate on the left and retains the original stalk
point, so the two orders of these operations agree directly. `familyMap_apply`
records this formula. `familyFunctor` bundles the family sheaves and these
maps, using the identity and composition laws of the actual stalk functors.
The formula itself does not require continuity of translations.

`coinducedZeroFunctor` is the composite of the equivariant Godement
`zeroFunctor`, the functor `toSheaf` forgetting equivariance, and
`coinduction`. Its objects are definitionally the existing `coinducedZero F`.
`read_map_hom` proves

```
read F' U (coinducedZeroFunctor.map a (s))(g,y)
  = a_y(read F U s(g,y)).
```

The proof evaluates `read_arrow` on the full translated open
`coordinateOpen U g`. Naturality of the coinduced sheaf map moves that map
across `coordinateArrow U g`; naturality of the right Kan counit then gives
the induced ordinary stalk-family map. Thus `coinducedZeroNatIso` assembles
the existing coordinate isomorphisms into a natural isomorphism
`coinducedZeroFunctor ≅ familyFunctor`.

## The coaugmentation and its actual germs

`coinduction_counit_hom` identifies the counit of the published sheaf
coinduction adjunction with the underlying right Kan counit. This follows
from the definitions of the transport-sheaf equivalence and adjunction,
and Mathlib's sheaf and right Kan counit identities.

`coinducedCoaugmentation` first applies the existing equivariant
Godement coaugmentation `F ⟶ zeroSheaf F.obj`, and then the coinduction
unit at that zero sheaf. Its target is `coinducedZeroFunctor.obj F`.
`coinducedCoaugmentation_counit` states that applying `toSheaf` and then
the coinduction counit recovers the original ordinary family of germs.
The proof is the left triangle identity at the actual zero sheaf.

For `g • y ∈ U`, let `W = coordinateOpen U g`, so
`W = {z | g • z ∈ U}`. The arrow `coordinateArrow U g` has label `g`
and source the ordinary open `W`. For an original section `s` of `F` on
`U`, `read_coinducedCoaugmentation` proves the precise coordinate formula

```
read F U (coinducedCoaugmentation.app F (s))(g,y)
  = germ at y on W of (F.map (coordinateArrow U g).op (s)).
```

The right side is a germ in `F_y`. In particular it is formed after the
original labelled section transport; it does not silently replace it by a
germ at `g • y`. The implemented proof evaluates `read_arrow`, uses
naturality of the coaugmentation on `coordinateArrow U g`, and then uses
the counit identity above.

## Retained boundaries

These are functorial constructions on ordinary-open equivariant sheaves.
They do not construct spatial maps, compare full and smooth Godement
functors, prove exactness or a resolution comparison, or give an analytic,
etale, arithmetic or Shimura realization. Those remain separate parts of
the Harris framework.
