# Actual integral Weil points over all upper function-field completions

This unit constructs the local integral Weil point homeomorphism for a
quasi-projective model over the **actual integral closure** of an original
function-field valuation ring. Its factors range over every actual upper
place, and both sides have independently constructed scheme point topologies.

## Source and hypotheses

Brian Conrad, *Weil and Grothendieck approaches to adelic points*, December 31,
2011, Example 4.2, printed p.10, passes from integral models and local complete
rings to the adelic Weil homeomorphism. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
This module supplies the local integral point comparison for the original
valuation-ring normalization. Spreading models and compatibility with global
choices are retained as separate obligations.

The fields `k`, `K` and `L` lie in one arbitrary universe, with finite `k`,
their three algebra structures, `FiniteDimensional K L`,
`IsScalarTower k K L`, an original `Algebra (RatFunc k) K` presentation,
`IsScalarTower k (RatFunc k) K`, and `FunctionField k K`. Fix any original
place `v`. Write `R = v.toValuationSubring`,
`S = curvePlaceIntegralClosure L v`, `Op = curvePlaceCompletionIntegers v`,
and `Oq = curvePlaceCompletionIntegers q.1`.

The original integral model is `Y : Over (Spec S)` with
`LocallyOfFiniteType Y.hom`. Its concrete quasi-projective data are `n`, an
actual morphism `j : Y.left -> ProjectiveSpace S n`, `IsImmersion j`, and
compatibility of its composite with the original structure map. No
separability, selected upper-place subfamily, assumed integral tensor
isomorphism, finite upper module premise or module-topology premise is used.
No global integral model or upper rational-function presentation is supplied.

## Constructed point homeomorphism

In `Langlands.AlgebraicGeometry.PointTopology`,
`functionFieldIntegralWeilRestrictionPointHomeomorph` has source
`RingPoint R (affineChartWeilRestriction R S Y) Op` and target
`forall q : CurvePlacesAbove k L v, RingPoint S Y Oq`.
These are actual scheme-valued points over the original rings and the actual
constructed Weil scheme. The source carries `schemePointTopology` for the
Weil scheme. Each factor carries `schemePointTopology` for `Y`, and the target
has their product topology. The topologies are defined independently of the
comparison.

The original `S/R` is module finite by the proved normalization construction.
It is torsion free over the lower DVR, so the private
`integralClosureProjective` instance derives projectivity. The actual
`integralTensorEquiv v` supplies `Op tensor_R S` as the product of the original
upper `Oq`, with its original coefficient formula.
`CurvePlaceIntegralTopology` derives the finite and projective module
properties of every `Oq/Op`, their finite-module topologies and the inherited
topological ring and open-unit properties of the integer rings. The existing
generic `projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph`
therefore applies. The actual projective immersion supplies all its finite
affine-neighborhood and separatedness inputs internally.

## Original counit law

`functionFieldIntegralWeilRestrictionPointHomeomorph_counit` states the
original `q` component formula. It is the original
`affineChartWeilRestrictionComparison R S Y` at the `Op` test spectrum,
precomposed with the actual
`completedTensorWeilRestrictionFactorTestMap` determined by the integral
tensor decomposition and the original `q` factor. The tensor pure-component
formula uses the original completed-integer embedding and original upper-field
completion image of an integral-closure element. The comparison is thus the
intended relative Weil counit on these actual integer points.

The implemented proof first compares the wrapper homeomorphism with its
generic construction, then rewrites before applying the generic counit law.
This bounds definitional reduction and uses the default heartbeat limit.

## Scope retained

All original finite field extensions and inseparable rational presentations
are retained. The actual integral tensor isomorphism, local finiteness,
projectivity and original module topologies are proved, rather than fields of
an assumed package. This unit does not prove spreading to a common global
integral model, compatibility with the completed-field homeomorphism, or the
global adelic Weil homeomorphism. Those remain parent-task obligations, as do
the separate Section 5 algebraic-space conclusions.
