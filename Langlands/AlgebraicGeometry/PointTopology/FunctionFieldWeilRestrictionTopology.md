# Actual function-field Weil point topology over all upper completions

This module constructs the local Weil-restriction point homeomorphism for
actual global function fields, with a product indexed by every actual upper
curve place. Both sides carry their independently constructed scheme point
topologies. The component law retains the original Weil counit.

## Original source and hypotheses

Brian Conrad, *Weil and Grothendieck approaches to adelic points*, December 31,
2011, Example 4.2, printed p.10, reduces the quasi-projective adelic Weil
comparison to the product over upper completions and then to finite extensions
of complete fields. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
This module supplies the function-field local point homeomorphism in that
reduction. It does not by itself assert the integral or adelic comparison.

The fields `k`, `K` and `L` lie in one arbitrary common universe. The inputs
are finite `k`, their three algebra structures, `FiniteDimensional K L`,
`IsScalarTower k K L`, an original `Algebra (RatFunc k) K` presentation,
`IsScalarTower k (RatFunc k) K`, and `FunctionField k K`. No separability of
`L/K` or of the given rational-function presentation is imposed.

The original upper scheme is `Y : Over (Spec L)` with
`LocallyOfFiniteType Y.hom`. Quasi-projectivity is expressed concretely by an
integer `n`, an actual morphism `j : Y.left -> ProjectiveSpace L n`, an
`IsImmersion j` instance, and equality of its composite structure map with
`Y.hom`. The lower place `v : AlgebraicCurve.Place k K` is arbitrary. Neither a
chosen upper-place subfamily nor an assumed tensor decomposition is provided.
The product is over the entire `CurvePlacesAbove k L v`, which consists of
original discrete places whose valuation subring restricts exactly to that
of `v`. Its finiteness and the finite local extension degrees are proved by
the imported arithmetic construction.

## Point spaces and their topologies

`functionFieldWeilRestrictionPointHomeomorph` is defined in
`Langlands.AlgebraicGeometry.PointTopology`. Its source is the actual
`RingPoint K (affineChartWeilRestriction K L Y) (curvePlaceCompletion v)`.
Its target is the dependent product of the original
`RingPoint L Y (curvePlaceCompletion q.1)` over every upper place `q`.
`RingPoint` denotes actual scheme morphisms from the corresponding coefficient
spectrum over the original field. `affineChartWeilRestriction` is the existing
constructed scheme representing the Weil functor for targets with finite
sets in affine neighborhoods.

The source topology is `schemePointTopology` for that actual lower Weil
scheme. Each target factor has `schemePointTopology` for `Y`, and the target
has their product topology. These topologies are defined independently of the
homeomorphism. The hypotheses about finite affine neighborhoods and
separatedness required at intermediate stages are derived from the actual
projective immersion by the existing generic construction; they are not
extra inputs for the user.

## Implemented comparison

The private `functionFieldFactorIsModuleTopology` proves that the topology on
each actual upper completion is its finite-dimensional module topology over
the actual lower completion. A rank-one witness for the original discrete
valuation equips the lower completion with a compatible nontrivial norm while
retaining its topology. Completeness, the proved finite local degree and the
continuous scalar action give `isModuleTopologyOfFiniteDimensional`. The
helper itself needs no finite-constant or rational-presentation hypothesis;
these enter only when the global tensor decomposition is used.

`functionFieldWeilRestrictionPointHomeomorph` then applies the existing
`projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph` to
`CurvePlaceCompletedTensorEquiv.allTensorEquiv v` and its original-field
pure-tensor formula. The finite/projective module structures on the field
extensions are derived. The reused construction composes tensor base change,
coefficient transport, finite-product decomposition and the local Weil point
comparison, with their proved geometric and topological compatibility.

`functionFieldWeilRestrictionPointHomeomorph_counit` fixes the actual map. Its
`q` component equals the original
`affineChartWeilRestrictionComparison K L Y` at the lower completed-field test
spectrum, precomposed with
`completedTensorWeilRestrictionFactorTestMap` for that original `q` factor.
The latter uses the actual tensor equivalence, whose `a tensor x` component is
`completionMap v q a * algebraMap L (curvePlaceCompletion q.1) x`.
The proof compares the wrapper and the generic homeomorphism before applying
them to a point, then invokes the generic counit law. This avoids reducing the
large composite comparison during elaboration; no additional heartbeat limit
is used.

## Reuse and remaining obligations

This is a concrete function-field specialization of the previously constructed
generic Weil point comparison. It uses the proved actual arithmetic tensor
decomposition and all upper completions, with arbitrary original inseparable
presentations. It provides neither an integral-model comparison nor a global
adelic-limit homeomorphism. Those remain obligations of the parent task, as do
the separate algebraic-space assertions of Section 5.
