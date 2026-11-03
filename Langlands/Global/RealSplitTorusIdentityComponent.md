# Real identity components of actual split tori

This internal construction defines the subgroup of actual coefficient points
on which every base-field character is positive. For a supplied split torus
over a conditionally complete ordered coefficient field, it proves that this
subgroup is exactly the connected component of the identity, with the existing
regular-function topology on actual affine points.

## Objects and hypotheses

The base field `F`, the coefficient field `A` and the finite splitting index
type `I` lie in an arbitrary common universe `u`. The commutative group scheme
`T` is over `Spec F`, and `A` has a supplied `F`-algebra structure.

The definition `orderedCoefficientPositiveSubgroup F T A` only requires
`Field A`, `LinearOrder A` and `IsStrictOrderedRing A` in addition to these
algebraic data. It is the intersection, over all actual characters
`χ : characterLattice T`, of the inverse images of `Units.posSubgroup A`
under the existing homomorphisms `characterHom F T A χ`. Thus its membership
condition is

```text
for every F-rational character χ of T, 0 < (χ(x) : A).
```

The definition does not require splitness, a choice of coordinates, a topology,
or a number-field structure.

The coordinate comparison assumes a supplied isomorphism of actual group
schemes

```text
e : T.toGrp ≅ splitTorus (Spec F) I
```

with `Fintype I`. The identity-component comparison additionally assumes
`ConditionallyCompleteLinearOrder A`, `TopologicalSpace A`,
`OrderTopology A`, `IsTopologicalRing A` and `ContinuousInv₀ A`, retaining
the ordered-field and algebra structures. Its point-space topology is exactly
`GroupScheme.affinePointsTopologicalSpace T.toGrp (CommAlgCat.of F A)`.
No new topology on those points is introduced.

For universe-zero fields with a specified real algebra structure, `A = ℝ`
is the usual real-point specialization. The theorem does not assert that an
arbitrary base field admits an embedding into `ℝ`. Its generic coefficient
formulation also permits coefficient models in higher universes whenever the
displayed structures are supplied.

## Construction laws and implemented arguments

`positiveUnitMap A` maps the units of the nonnegative subsemiring into `Aˣ`
using `Units.map` of the actual inclusion. `range_positiveUnitMap` identifies
its range with `Units.posSubgroup A`: a nonnegative unit is positive, and a
positive unit lifts via `Nonneg.unitsEquivPos`. The inclusion is continuous by
`Continuous.units_map`.

`isClopen_posSubgroup` proves that positive units are open and closed using
the continuous value map. Positivity is the inverse image of `(0, ∞)`;
its complement within the units is the inverse image of `(-∞, 0)`, because
a unit never has value zero. This requires order topology but does not
require order completeness or continuous inversion.

For the complete ordered coefficient field,
`Nonneg.unitsHomeomorphPos A` and connectedness of `(0, ∞)` give connectedness
of the units of the nonnegative subsemiring. The connected range of
`positiveUnitMap A` is therefore the positive-unit subgroup. Its connectedness
and the fact that it contains `1` put it inside the identity component.
Conversely, its clopenness and membership of `1` put the identity component
inside it. This proves `connectedComponent_one_units`.

`mem_orderedCoefficientPositiveSubgroup_iff_coordinates` proves that the
intrinsic condition is equivalent to positivity of every coordinate of `e`.
For one direction it evaluates the actual coordinate characters
`coordinateCharacter F I T e i`. For the other it uses the imported actual
monomial formula `characterValue_eq_prod`: the positive-unit subgroup is
closed under integer powers and finite products. This argument needs no
topology or completeness.

`connectedComponent_one_eq_orderedCoefficientPositiveSubgroup` proves the
equality of subsets of the actual point group

```text
connectedComponent (1 : Lie.AffinePoints T.toGrp A)
  = ↑(orderedCoefficientPositiveSubgroup F T A).
```

Both directions transport membership through the genuine coordinate
homeomorphism already constructed in
[PositiveRealTorusEmbedding](PositiveRealTorusEmbedding.md).
Continuity maps a point in the identity component to the identity component
of `(I → Aˣ)`. The theorem `connectedComponent_pi` computes this component
coordinatewise, and `connectedComponent_one_units` computes each factor.
For the converse, continuity of the inverse coordinates maps the positive
coordinate tuple back to the original point in the actual identity component.
The homomorphisms take `1` to `1` in each direction.

The two `mem_connectedComponent_one_iff_*` corollaries give characterwise
and coordinatewise membership tests. The final two lemmas give connectedness
and closedness of the intrinsic positive subgroup from its proved equality
with the actual identity component. Empty `I` is allowed throughout, so the
rank-zero case is retained. Intrinsic positivity is independent of the supplied
splitting because its definition quantifies over characters.

## Provenance and scope

This is internal infrastructure. It uses the existing actual character
evaluation, split-torus monomial formula and coordinate homeomorphism,
together with elementary ordered and connected topology from Mathlib.
It is not a translation of a new theorem from the automorphic literature.

It does not construct restriction of scalars or identify a greatest
`ℚ`-split central torus. It supplies no comparison between real coefficient
points and the positive scalar adelic subgroup, no unconditional reductive
positive/norm-one decomposition, and no Haar-measure, height, reduction-theory
or finite-volume assertion. Those comparisons and structural assertions
remain separate obligations of the general adelic program.
