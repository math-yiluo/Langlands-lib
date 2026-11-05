# Forward continuity of the affine Weil-restriction point comparison

The published module `AffineWeilRestrictionTopology` makes the canonical
comparison between the `A`-points of `AffineWeil.groupScheme A B G` and the
`B`-points of `G` a homeomorphism. It assumes topological rings and
`[IsModuleTopology A B]`. The intended application is over the maximal
unramified extension `K` of a nonarchimedean local field, as in
Kaletha-Prasad Section 2.5, with `B = L` a finite Galois extension of `K`.
That field `K` is not complete. The published complete-field adapter
`CompleteFieldWeilRestrictionTopology` obtains the `IsModuleTopology K L`
instance from completeness of `K`, so it cannot be invoked directly there.
This does not mean that noncompleteness rules out a module topology. For
example, Mathlib provides `IsModuleTopology A A` for every topological ring
`A`. This module avoids the question. It proves only the forward direction:
the comparison is continuous whenever scalar multiplication `A × B → B` and
addition on `B` are continuous. No topological ring structure on `A` and no
module topology on `B` is assumed. Continuity of the inverse is not claimed.

## Common setup

`A` and `B` are commutative rings and `B` is an `A`-algebra that is finite
and projective as an `A`-module (`Module.Finite A B`, `Module.Projective A B`).
These are the algebraic hypotheses of the published Weil-restriction
construction, and they are kept unchanged. The scheme, group and
rational-point results take `A` and `B` in one arbitrary universe `u`. Only
the topological hypotheses are weakened: `A` and `B` carry topologies with
`ContinuousSMul A B` and `ContinuousAdd B`.

The content is internal. It reuses the published constructions, and its
proofs copy the published forward-continuity argument with weaker hypotheses.

`continuous_weilRestrictionAlgPointEquiv_of_continuousSMul` is the algebra-point
version, for a commutative `B`-algebra `C` of finite type
(`Algebra.FiniteType B C`). It states that
`weilRestrictionAlgPointEquiv A B C` is continuous. Its proof is the
published `continuous_weilRestrictionAlgPointEquiv` argument. Every coordinate of the image point is
`Algebra.TensorProduct.rid A B B` applied to a tensor in
`B ⊗[A] WeilRestrictionFiniteType A B C`, evaluated at the varying point.
The proof uses induction on that tensor. On a pure tensor `b ⊗ w` the
coordinate is `p w • b`, which is continuous because evaluation at `w` is
continuous and `A × B → B` is continuous. Sums are handled by continuity of
addition on `B`. The published module uses its module topology only for these
two facts.

For an affine scheme `X` over `Spec B` that is locally of finite type, with
`B` finite projective over `A` as above,
`affineWeilRestrictionPointContinuousMap` is the same base-point map on the
named global-section point carriers. It is the composite of the published
spectrum-to-algebra point homeomorphism, the algebra-point map above, and the
inverse of the published affine-scheme point homeomorphism.
`affineWeilRestrictionPointContinuousMap_apply` gives its formula in
global-section coordinates.

For an actual group scheme `G` over `Spec B` with affine underlying scheme and
locally finite-type structure map, again with `B` finite projective over `A`,
`basePointsEquiv_eq_continuousMap` proves
that the published multiplicative comparison `AffineWeil.basePointsEquiv A B G`
agrees pointwise with this continuous map. The proof uses the published
coordinate formula `basePointsEquiv_coordinates` and requires no topology.
`continuous_basePointsEquiv_of_continuousSMul` then proves that
`basePointsEquiv A B G` is continuous between the existing evaluation
topologies `affinePointsTopologicalSpace` on both point groups. It uses the
published identity homeomorphisms `affinePointsRingPointHomeomorph`.

Over fields `A` and `B` with `B` finite-dimensional over `A`,
`continuous_rationalBasePoints_of_continuousSMul` gives the corresponding
statement for rational points. The map sends a rational point `x` of the Weil
restriction to
`(rationalCoeffEquiv B G).symm (basePointsEquiv A B G (rationalCoeffEquiv A _ x))`,
using the published rational coefficient equivalences from
`GaloisPointRational`. It is continuous from `rationalPointTopology A` of the
Weil restriction to `rationalPointTopology B` of `G`. The two coefficient
equivalences agree pointwise with the published homeomorphisms
`rationalPointsAffineHomeomorph`, by `rationalCoeffEquiv_eq`, so the composite
is continuous.

The module proves no openness, smoothness, norm, or adelic statement. It does
not show that the comparison is a homeomorphism under these weaker
hypotheses.
