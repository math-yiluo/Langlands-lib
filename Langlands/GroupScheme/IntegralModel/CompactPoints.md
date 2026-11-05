# Compact images of actual integral model sections

This internal prerequisite uses a supplied `IntegralModel R K G`, the actual
coefficient inclusion `algebraMap R K`, and the existing regular-function
evaluation topologies. It does not construct an integral model.

The integral-point map agrees with the composite of coefficient extension on
the model's actual points, the canonical generic-fibre point comparison, and
the supplied generic isomorphism. The proof checks the two projections of
the defining pullback. This identifies the original section map, rather than
introducing a replacement map or point carrier.

When `K` is a topological ring and the inclusion `R → K` is continuous, this
composite proves continuity of `integralPointMap`. If `R` is a compact
Hausdorff topological ring, the published finite-type affine point compactness
theorem gives compactness of the integral sections. Their continuous image
`integralPoints` is therefore compact in the named rational-point topology
of `G`.

`integralPointContinuousHom` bundles the same point map as a continuous
homomorphism. For a model of the scalar extension of a group over a smaller
field `k`, the published canonical coefficient-point comparison also proves
continuity of `coefficientPointMap k K` and compactness of
`coefficientIntegralPoints k K` in the original group's actual `K`-point
evaluation topology.

The affineness of `G` is explicit in these topology statements. Affineness and
finite type of the model are already fields of `IntegralModel`. The argument
requires no smoothness or reductivity. It proves no maximality or parabolic
covering assertion.

All results are derived from the published actual model map, point-comparison
homeomorphisms, coefficient-map continuity, and affine-point compactness.
There is no additional external mathematical input.
