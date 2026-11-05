# Continuous group comparison for affine Weil restriction

Let `A` and `B` be commutative rings in the same arbitrary universe, with `B`
finite projective over `A`. Let `G` be an actual group scheme over `Spec B`
with affine underlying scheme and locally finite-type structural morphism.
This module equips the canonical multiplicative comparison between the actual
`A`-points of `AffineWeil.groupScheme A B G` and the actual `B`-points of `G`
with continuity in both directions.

The construction is internal to the existing Library interfaces. Its
multiplicativity comes from the original group-object point laws and
`AffineWeil.pointsEquiv`. Its topology comes from the already published
`PointTopology.affineWeilRestrictionPointHomeomorph`. The latter's topology
theorem and source provenance are documented in its own paired Markdown.
No new external structural assertion is assumed here.

`tensorUnitPointsEquiv` applies the original group's affine-point functor to
the actual coefficient-algebra isomorphism
`Algebra.TensorProduct.rid A B B : B ⊗[A] A ≃ₐ[B] B`.
`tensorUnitPointsEquiv_apply` identifies this with the original coefficient
change. `basePointsEquiv` composes it with `pointsEquiv A B G A`, giving a
multiplicative equivalence on the actual scheme-point groups without any
topological assumptions.

`basePointsEquiv_coordinates` states its exact coordinate formula:
`WeilRestrictionFiniteType.homEquiv` applied to the restricted point's algebra
map, followed by the tensor-unit map. It follows by coefficient naturality of
the original global-section coordinates and `pointsEquiv_coordinates`.
After adding topological ring structures and `[IsModuleTopology A B]`,
`basePointsEquiv_eq` compares this formula with the published
`affineWeilRestrictionPointHomeomorph_apply` formula, proving equality of the
actual point maps.

Both actual point groups keep their existing `affinePointsTopologicalSpace`,
defined by evaluation of all global regular functions. The named general
affine-scheme point carriers already have their own global-section evaluation
topologies. `basePointsHomeomorph` composes the published scheme-level
homeomorphism with the existing `affinePointsRingPointHomeomorph` on either
side. These last two homeomorphisms are the identity on actual relative
morphisms, as `basePointsHomeomorph_apply` records. No point topology is defined
by transport along the Weil-restriction bijection.

`isHomeomorph_basePointsEquiv` follows from equality with this homeomorphism,
and `basePointsContinuousEquiv` bundles the multiplicative equivalence with
continuity of it and its inverse. Its apply theorem again identifies its map
with the original scheme-level homeomorphism. There is no additional
continuity premise on the algebra structure map, and no Hausdorff or local
compactness hypothesis is added.

This comparison concerns base-ring points. It does not prove an adelic tensor
decomposition, any measure comparison, preservation of reductivity or
smoothness, or a rational split-centre theorem.
