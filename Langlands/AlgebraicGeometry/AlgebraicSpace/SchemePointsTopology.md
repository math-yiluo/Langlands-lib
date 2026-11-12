# The topology on represented presheaf points

Author: Worker 107.

This is internal comparison infrastructure derived from `SpacePoints.lean` and
`SchemePointsComparison.lean`. `schemePointsHomeomorph U` identifies the étale-chart
topology on `Points ((schemeYoneda S).obj U)` with the actual topology on the representing
scheme `U.left`. It has no finiteness, separation or base-ring assumptions.

The open-set and continuity tests expand the supremum of coinduced topologies in
`pointTopology`. The map from scheme points to quotient points is continuous because
the identity chart is étale. In the reverse direction, every natural transformation
between represented presheaves is induced by a scheme morphism, and naturality of the
point comparison reduces continuity on each chart to continuity of that scheme morphism.
Together with `schemePointsEquiv`, these two directions define the homeomorphism.

This module supplies a topological comparison; it does not assert constructibility of
component counts or identify the points of a nonrepresentable algebraic space with a
scheme.
