# The split-centre subgroup from a rational torus in the Weil restriction

Author: Worker 112.

Getz--Hahn (2.20), p. 68, define `A_G` for a number field `F`. It is the
neutral component of the real points of the greatest `ℚ`-split torus in
`Res_{F/ℚ} Z_G`, viewed inside `G(F_∞) < G(A_F)`. Display (2.21), p. 69, then
forms `[G] = A_G G(F) \ G(A_F)`. Source:
`getz-hahn-2024-automorphic-representations`.

This module expresses centrality by a central morphism into the restriction
`Res_{F/ℚ} G` itself. It does not construct `Res_{F/ℚ} Z_G` and does not
prove that it is the centre of `Res_{F/ℚ} G`.

This module defines the subgroup and quotient of that shape for supplied
data:

- `F` is a number field in universe zero;
- `G` is an affine group scheme over `F` that is locally of finite type;
- `S` is a commutative group scheme over `ℚ`;
- `j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G` maps `S` into the published
  actual affine Weil restriction.

The definitions put no hypotheses on `j`. The Getz--Hahn case is when `j` is a
split component (`GroupScheme.IsSplitComponent j`): a central split torus that
is maximal under factorization. In that case `j` is all-test central in the
restriction. For split `S`, the existing module `RealSplitTorusIdentityComponent`
identifies `orderedCoefficientPositiveSubgroup ℚ S ℝ` with the neutral
component of `S(ℝ)`, using a supplied splitting. This module does not claim
that a split component exists or that it is unique.

## Definitions

- `positiveImageHom F G S j` is a composite of four maps:
  1. the inclusion of `orderedCoefficientPositiveSubgroup ℚ S ℝ`, the real
     points on which every rational character is positive;
  2. the point map of `j` on real points;
  3. the published `AdelicWeilRestriction.realPointsEquiv F G`, from real points
     of the restriction to `InfiniteAdelicGroupPoints F G`;
  4. `AdelicGroupPoints.ofInfinite`, which includes infinite points with
     finite part one.
- `subgroup F G S j` is its range in `AdelicGroupPoints F G`.
- `rationalSubgroup F G S j` is the join of this subgroup with the principal
  rational points `AdelicGroupPoints.rationalSubgroup F G`.
- `Quotient F G S j` is the existing nonnormal `LeftCosetSpace` of that join.
  It is the left quotient by the image and the principal points, with the
  convention of (2.21). It carries no topology here.

## Proved facts

- `positiveImageHom_apply` gives the composite on points. It holds by
  definition.
- `subgroup_le_rationalSubgroup` and `principal_le_rationalSubgroup` give the
  two inclusions into the join.
- `ofInfinite_mem_center`: an infinite point that is central stays central
  after inclusion with finite part one. The proof compares both products
  through the published infinite-finite product equivalence.
- `subgroup_le_center`: if `j` is all-test central (`IsCentral j`), the whole
  image is central in the adelic points. Each real image point is central in
  the real points of the restriction, and `realPointsEquiv` is a group
  isomorphism.
- `mem_rationalSubgroup_iff`: for central `j`, the image is normal, so an
  element of the join is a product of an image point and a principal point.

## Scope

This is internal construction infrastructure. No topology, closedness, measure
or finite-volume claim is made. The module does not identify this subgroup with
the existing image `PositiveRealTorus.imageSubgroup` of an `F`-split central
torus of `G`. That comparison is a separate proposition statement.
