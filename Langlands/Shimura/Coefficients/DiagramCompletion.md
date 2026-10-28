# Actual adic completion of varying-group coefficient diagrams

Author: Worker 13.

This internal construction completes an actual coefficient diagram, keeping its
varying group diagram fixed. The coefficient-power index is the full opposite
category of natural numbers, including zero, and is independent of the category
indexing the groups. The input ring, module carriers and group carriers share
universe `u`; the group-index object and morphism universes are independent.

The module functor `Langlands.Coefficients.AdicSystem.completionFunctor` uses
Mathlib's actual `AdicCompletion I M`, the module of compatible ideal-power
quotient sequences. Its maps are Mathlib's completion maps, restricted to the
original scalar ring. The identity and composition laws follow from the existing
completion-map laws. `completionProjection` is evaluation in the actual power
quotient and `completionUnit` is the canonical map from the original module.
Their composite is the genuine quotient map. These module constructions also
allow the module universe to be independent of the scalar-ring universe.

`coefficientDiagramCompletion` applies that functor to every module, group
action, transition and diagram morphism through the published
`EquivariantDiagram.mapFunctor`. Thus the completed action at each group index
is the original action followed by the actual completion map. All action laws,
transition equivariance and functor laws come from that published construction;
no desired limit action is input. The completed diagram has module
`AdicCompletion I (M.obj.obj j)` at `j`.

The module evaluations and unit lift to natural transformations
`coefficientDiagramCompletionProjection` and `coefficientDiagramCompletionUnit`
on the entire category of varying-group coefficient diagrams. The unit followed
by projection equals the published `coefficientDiagramPowerUnit`. Compatibility
of completion evaluations with the genuine power transitions follows from the
compatible-sequence condition itself.

`coefficientDiagramCompletionCone` has the completed diagram as its vertex and
the actual evaluations as its legs. It is a cone on the published
`coefficientDiagramReductionFunctor`, whose terms are genuine module quotients.
For any cone `s`, `coefficientDiagramCompletionLift` applies the actual module
completion lift at every group index. The cone equations prove that its values
are compatible sequences. Naturality and equivariance of its legs prove that
this family of lifts is a morphism of varying-group diagrams. Its composites
with evaluations are exactly the legs of `s`.

`coefficientDiagramCompletionConeIsLimit` proves the universal property of this
same cone in `EquivariantDiagram`. Uniqueness is checked at every group index
and every power evaluation, using extensionality of the actual completion.
Every completion projection is surjective on each underlying module, by the
existing evaluation-surjectivity theorem; no surjectivity of a limit over the
group index is claimed.

The provenance is internal: the published `AdicSystem` and
`VaryingCoverReduction` supply the actual quotient systems,
`EquivariantDiagramFunctor` supplies postcomposition, and pinned Mathlib
`RingTheory/AdicCompletion/Functoriality.lean` supplies the actual completion
and its functorial laws. The construction takes no limit over the group-index
category and assumes neither adic completeness of the original modules nor
finiteness of the groups. It asserts no topology, smoothness, identification
with the original diagram, lisse-adic sheaf, associated-sheaf comparison or
cohomological comparison. Those further interfaces remain separate obligations.
