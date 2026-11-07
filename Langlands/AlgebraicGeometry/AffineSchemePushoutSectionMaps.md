# Spectrum section-map comparisons

This internal construction uses arbitrary `B C D : CommRingCat.{u}` and
actual morphisms `f : B ⟶ D` and `g : C ⟶ D`. Write `P` for
`RingHom.pullback f.hom g.hom`, and `i : P ⟶ B`, `j : P ⟶ C` for its
canonical projections, bundled in `CommRingCat`. It identifies the section maps
of the actual spectrum morphisms with the maps of the presheaf pullback in
`AffineSchemePushoutSheaf`.

The construction assumes no surjectivity, nontriviality, or geometric property.
The second comparison and the resulting witness take any proof

```text
h : Spec.topMap g ≫ Spec.topMap j = Spec.topMap f ≫ Spec.topMap i.
```

This equality fixes the equality transport to the common pushforward presheaf;
its choice does not introduce an additional mathematical constraint on the
canonical commuting ring square.

## Comparisons

`specPushforwardFst_eq` identifies the pushforward of the section map of
`Spec.sheafedSpaceMap f` along `Spec.topMap i` with
`(overSheafFst f.hom g.hom).hom`. This identity holds definitionally.

`specPushforwardSnd_eq` identifies the pushforward of the section map of
`Spec.sheafedSpaceMap g` along `Spec.topMap j`, followed by
`(pushforwardEq h (Spec.structureSheaf D).obj).hom`, with
`(overSheafSnd f.hom g.hom).hom`. The implemented proof uses extensionality
of natural transformations and commutative-ring morphisms. On each open set,
`pushforwardEq_hom_app` expresses the equality transport as a restriction.
`StructureSheaf.comap_id_eq_map` replaces this restriction by a comap for
the identity ring map. `StructureSheaf.comap_comp` combines it with the comap
for `g`. The remaining equality of inverse-image opens follows from `h`.

## Pullback witness

`isPullback_specPresheaf` has the actual section maps of
`Spec.sheafedSpaceMap i` and `Spec.sheafedSpaceMap j` as its incoming legs.
Its outgoing legs are the pushed section maps for `f` and `g`, with the second
transported by `pushforwardEq h` as above. Rewriting these outgoing maps with
the two comparison identities gives precisely `isPullback_overPresheaf`.
The incoming maps agree definitionally with `overSheafInl` and `overSheafInr`
after forgetting sheafness.

`specPresheafPullbackIsLimit` constructs the `IsLimit` witness for the
`PullbackCone.mk` with these same incoming maps and the commutativity proof
from `isPullback_specPresheaf`. Thus the cone point is the actual structure
presheaf of `Spec P`, and the limit property concerns arbitrary cones of
commutative-ring-valued presheaves on `Spec P`.

## Provenance and use

These are internal adapters derived from the imported sheaf pullback theorem
and Mathlib's actual spectrum, pushforward, restriction, and structure-sheaf
comap constructions. Worker 1568 supplied the sheaf comparison and the
required equality-transport interface; Worker 336 implemented the comparisons
and the limit witness. No external source theorem is asserted here.

The generic presheafed-space universal property and the exact scheme theorem
are separate steps. This module supplies their section-map input; it does not
assert a pushout of schemes.
