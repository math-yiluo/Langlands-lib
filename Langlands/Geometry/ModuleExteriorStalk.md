# Exterior powers and actual module stalks

This module constructs the comparison between the stalk of a sectionwise
exterior power and the exterior power of an actual module stalk. It also
constructs the exterior-power sheaf by sheafification and identifies its stalks.

## Provenance and scope

This is internal infrastructure for the independent exterior-subsheaf
comparison needed by the Deligne determinant condition. The definitions use
Mathlib's actual module exterior power, open-neighborhood colimits and
sheafification. The proofs below are a direct finite-neighborhood argument
implemented here; no original-literature theorem is asserted by this module.

The assumptions are a commutative ring `R : Type u`, a topological space
`X : TopCat.{u}`, a presheaf `M` valued in `ModuleCat.{u} R`, a point `x : X`
and any natural number `n`, including zero. The original presheaf need not be
a sheaf, locally free or finitely generated. No assumption on the topology,
field of coefficients, or characteristic is used. All spaces and modules use
the indicated common universe.

This module constructs no exterior subsheaf of an ambient rational sheaf and
proves no determinant-condition equivalence. Those are subsequent consumers.
It asserts no formal-module comparison, representability or level-covering
property.

## Common neighborhoods

`exists_fin_germs_eq` represents an arbitrary `Fin n` family of actual module
stalk elements by sections on one open neighborhood of `x`. Its induction
starts with the whole space for an empty family. For a successor, it chooses
a representative of the first germ and intersects that neighborhood with the
one representing the remaining family.

`fin_germ_eq` says that two such families with equal corresponding germs
restrict to equal sections on one common open neighborhood. It similarly
intersects the neighborhoods witnessing equality of the first pair and the
remaining pairs. Restriction functoriality and uniqueness of open inclusions
identify the resulting maps.

## Exterior presheaf and comparison

`exteriorPresheaf M n` applies `ModuleCat.exteriorPower.functor R n`
sectionwise. The canonical `exteriorStalkMap M x n` has type

```text
stalk (exteriorPresheaf M n) x  -->  exteriorPower (stalk M x) n.
```

It is the colimit descent of the exterior powers of the actual germ maps.
Naturality of the cocone follows from the restriction identity for germs.
`exteriorStalkMap_germ` states the resulting equality of module morphisms
on every open neighborhood; in particular an exterior product of sections
maps to the exterior product of their germs.

The private `exteriorGerm` chooses simultaneous representatives of a tuple
of germs and takes the germ of their exterior product. Its independence of
these choices is proved by `fin_germ_eq` and restriction compatibility of
exterior powers. `exteriorStalkAlternating` packages this as an alternating
map on the actual stalk. For additivity or scalar multiplication in one
coordinate, the proof represents the entire tuple and the additional
coordinate values on a common neighborhood, then applies the corresponding
sectionwise exterior identity. When two germ coordinates agree, one chosen
section is replaced by the other without changing any of the germs; the
resulting exterior product is zero by alternation.

`exteriorStalkAlternating_germs` computes this map on any simultaneous
representatives. `exteriorStalkInv` is induced by its universal alternating
property, with generator formula `exteriorStalkInv_mk`.
`exteriorStalkMap_alternating` gives the formula in the other direction.

`exteriorStalkMap_inv` and `exteriorStalkInv_map` prove both compositions are
identities. For the actual stalk the proof tests every germ morphism, then
tests exterior generators on each neighborhood. For the exterior power of
the stalk it tests exterior generators directly. These two morphisms define
`exteriorStalkIso M x n`. `exteriorStalkMap_naturality` proves its forward
map commutes with every morphism of the original presheaves, by testing
germ morphisms and applying exterior functoriality.

## Sheafification

`exteriorSheaf M n` is the actual sheafification of `exteriorPresheaf M n`.
`exteriorSheafStalkIso M x n` identifies its stalk with the exterior power
of the original stalk. It composes the inverse of the isomorphism induced
on stalks by Mathlib's actual sheafification unit with `exteriorStalkIso`.

`toSheafify_exteriorSheafStalkIso` identifies this composition with the
canonical presheaf stalk map. `exteriorSheafStalkIso_germ` further states
that the sheafification unit on an open set, followed by its actual germ
map and this comparison, is the exterior power of the original germ map.
Thus the comparison has a specified value on the sheafified exterior
products of actual sections, including in exterior degree zero.
