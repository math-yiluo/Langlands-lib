# Finite type from structural atlases

This internal supporting unit uses the published algebraic-space morphism
predicates and finite-presentation chart construction. It proves no new
limit-descent clause.

`SchemePullbackChart.scheme` is the actual scheme representing the overlap of a
source scheme chart with a scheme test map into the target space. Its map to
the presheaf fibre product is induced by the source chart and the identity of
the test scheme. Base-change stability shows that it is étale and surjective
whenever the source chart is. For an affine base and two affine scheme charts,
quasi-separatedness of the target makes the represented overlap quasi-compact:
the pairing into the affine product is a base change of the target diagonal.
Here `CompactSpace` means quasi-compactness, with no Hausdorff premise.

Consequently, over an affine base, a space with a quasi-compact structural
atlas has a quasi-compact morphism to every quasi-separated space. The proof
refines that atlas by a finite affine open cover, then uses the compact
represented overlaps above to meet every affine-test clause of
`IsQuasiCompactMorphism`.

When both spaces have locally finitely presented quasi-compact atlases and
the target is quasi-separated, the existing affine chart-square construction
also proves `IsLocallyOfFiniteTypeMorphism`. The chart's source is locally of
finite presentation over the base. Cancellation of its structure-map
factorization gives local finite type of the scheme chart map.

The final equivalence removes precisely these two finite-type conditions
from the published definition of properness. Under the same atlas hypotheses,
a morphism is proper exactly when it is separated and universally closed.
Universal closedness retains its original meaning on the points of every
scheme-tested presheaf fibre product. Its descent along limits remains an
independent obligation of the host task.

The base-change version applies this equivalence over any affine new base;
the existing structural-atlas and diagonal base-change theorems retain all
required premises.
