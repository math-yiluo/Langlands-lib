# Associated completed coefficients and the limit of associated quotients

Author: Worker 13.

This internal construction connects the actual algebraic completion of
varying-group coefficient diagrams with the ordinary coefficient-power limit
of their associated small-etale sheaf diagrams.

Fix a commutative ring `R`, an ideal `I`, a scheme `X`, a group diagram
`D : J ⥤ GrpCat`, and an equivariant diagram `Y` of actual small-etale covers
of `X`. Each `Y.action j` satisfies the published
`IsFiniteGeometricTorsor` predicate. The ring, scheme, groups and module
carriers share universe `u`; the object and morphism universes of `J` are
independent. The coefficient-power axis is the full opposite category of
natural numbers, including zero.

Write `A` for the published `etaleAssociatedVaryingSystemFunctor`, `C(M)` for
the actual completed coefficient diagram, and `P_n(M)` for the genuine
coefficient diagram modulo `I^n`. The functor
`etaleAssociatedCompletedCoefficientFunctor` is the composite `M ↦ A(C(M))`.
It retains the completed group actions, cover transitions and all morphisms
of coefficient diagrams from the imported constructions.

`etaleAssociatedCompletionCone` applies `A.mapCone` to the published
completion evaluation cone. Its vertex is `A(C(M))` and its leg at `n` is
exactly `A` of the genuine completion evaluation `C(M) → P_n(M)`, as stated
by `etaleAssociatedCompletionCone_π`. Its base is precisely the existing
system `n ↦ A(P_n(M))`.

`etaleAssociatedCompletionComparison` is the universal map from this cone
to the existing `etaleAssociatedCoefficientPowerLimit`. Thus its component
is the canonical morphism

`A(C(M)) → lim_n A(P_n(M))`.

Naturality in an arbitrary morphism of whole coefficient diagrams is proved
by composing with every limit projection. The resulting equality is `A`
applied to naturality of the actual completion evaluation.
`etaleAssociatedCompletionComparison_π` identifies every composite with a
limit projection as the corresponding mapped completion evaluation.

`etaleAssociatedCompletionComparison_unit` states an equality of natural
transformations: applying `A` to the original coefficient-diagram completion
unit, then composing with this comparison, gives the already published
`etaleAssociatedCoefficientPowerLimitUnit`. Its proof projects to each power,
uses functoriality of `A`, and applies the genuine completion-unit/evaluation
equation. `etaleAssociatedCompletionComparison_unique` characterizes the
comparison component among all maps with these projection equations.

`etaleAssociatedCompletionComparison_evaluation_π` gives the projection
equation after evaluating at any cover index `j` and using the published
isomorphism with the limit of the evaluated system. Consequently the equation
retains both the independent coefficient-power coordinate and the cover
coordinate.

The provenance is internal categorical composition of
[DiagramCompletion](DiagramCompletion.md),
[VaryingCoverInverse](VaryingCoverInverse.md) and
[VaryingCoverPowerLimits](VaryingCoverPowerLimits.md), using the ordinary
mapped cone and limit universal property. No new external-source assertion
is made. In particular, the mapped cone is not asserted to be limiting, and
the comparison is not asserted to be invertible. No preservation of infinite
limits by `A`, topology or smoothness of completed coefficients, limit over
`J`, lisse-adic identification, Harris-specific torsor construction, or
cohomological comparison is proved here. These remain separate obligations.
