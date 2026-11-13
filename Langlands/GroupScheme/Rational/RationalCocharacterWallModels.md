# Actual rank-one wall models with the original embedded Levi

This internal construction is over a field. The ambient group `G` is affine
and connected reductive, `a : A → L` is its supplied Levi's split component,
and the closed embedding `j : L → G` represents the centralizer of `a ≫ j`.
The rational directions `x,y,w` satisfy `IsWallDirection (a ≫ j) x y w`.

`WallModel` retains actual `RationalRankOneWallData` and the equality of its
outer Levi image with the full dynamic centralizer of the wall direction.
`IsWallDirection.wallModel` constructs it. Positive integral realizations of
the three directions give the outer dynamic parabolic and its reductive Levi.
The original `L` factors through that Levi because the whole-torus centralizer
lies in every cocharacter centralizer. For each regular endpoint, closed
subgroup pullback identifies its inner centralizer with the original `L`.
The fixed-Levi parabolic construction therefore supplies both inner parabolics
with exactly the original Levi source and ambient inclusion.

Endpoint containment is the wall nonnegative-root implication for smooth
connected affine `G`. Closed-subgroup pullback gives the exact intersections
on every test scheme. The wall root calculation identifies the inner
parabolics as opposites; their intersection is their common dynamic
centralizer, represented by the original `L`. A vanishing wall root and
endpoint regularity force properness. Proportional actual root pairings on
`A` yield maximality by the proved split-component maximality criterion.
Cancellation through the closed embedding of the outer Levi identifies its
torus map with `a` followed by the original inner Levi maps.

The provenance is internal: this combines actual dynamic decompositions,
regular endpoint centralizers, fixed-Levi reparametrization, wall root support,
and the split-component maximality theorem. It does not yet construct a
gallery, impose protection by a specified central torus, or prove the host
irreducible-induced-twist proposition.
