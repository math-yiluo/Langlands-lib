# Rational split centre of the restriction versus the split component of the group

Author: Worker 112.

`RestrictionSplitCentre.ComparisonStatement` is a proposition. It is stated,
not proved, here.

## Statement

The statement quantifies over the following data:

- a number field `F` in universe zero;
- an affine group scheme `G` over `F` that is locally of finite type;
- a commutative group scheme `S` over `ℚ` with a morphism
  `j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G` into the published actual
  affine Weil restriction;
- a commutative group scheme `T` over `F` with a morphism `i : T.toGrp ⟶ G`.

Assume `GroupScheme.IsSplitComponent j` (over `ℚ`) and
`GroupScheme.IsSplitComponent i` (over `F`). Then the statement asserts that
two subgroups of the actual adelic points `AdelicGroupPoints F G` are literally
equal:

- `RestrictionSplitCentre.subgroup F G S j`, the image of the positive real
  points of `S` through `j`, the canonical real-point comparison and
  inclusion at infinity;
- `PositiveRealTorus.imageSubgroup F T G i`, the existing image under `i` of
  `PositiveRealTorus.intrinsicSubgroup F T`: the adelic points of `T` at which
  every character takes a positive scalar idele value (the same positive real
  number at every infinite place, coordinate one at every finite place).

## Role and provenance

The first subgroup has the shape of `A_G` in Getz--Hahn (2.20), p. 68: the
neutral component of the real points of the greatest `ℚ`-split central torus
of `Res_{F/ℚ} G`. Source: `getz-hahn-2024-automorphic-representations`.

The second subgroup is the description of Mœglin--Waldspurger I.2.1. There,
positive reals are embedded equally at every archimedean place, with
coordinate one at the finite places, through the cocharacters of the split
centre over `F`. Source: `moeglin-waldspurger-1995-spectral-decomposition`.

The existing quotient, measure and reduction development uses the second
subgroup. This statement records the comparison that lets it be used with the
convention of (2.20).

The expected argument uses the restriction adjunction. A cocharacter of
`Res_{F/ℚ} G` over `ℚ` corresponds to a cocharacter of `G` over `F`. Because
`F/ℚ` is separable, centrality and closedness transfer in both directions.
The canonical real tensor equivalence `AdelicWeilRestriction.realTensorEquiv`
then sends `1 ⊗ t` to `t` at every infinite place. This is a proof route only. Nothing here proves it, and no
proof is attributed to the sources.

## Scope

The proposition asserts no existence of split components, no topology or
measure statement, and no reductivity. It does not equate a maximal `F`-split
torus with a greatest `ℚ`-split torus. Only their positive real images in the
adelic points are compared.
