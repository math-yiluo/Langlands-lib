# Integral split sources in neutral models of unit-fixed subsets

This internal construction starts with a split closed torus `iS : S → G`
over a nonarchimedean local field `F`, a supplied relative-component model
`N`, and a subset fixed by the unramified units of `S`. Assume that the
unramified base change of `N.full` contains the intersection of the ambient
character valuation kernel with the pointwise fixer of the subset.

`unitFixedNeutralTorusData` returns an actual split torus over `𝒪[F]`
with a closed inclusion into `N.neutral.group`. It also specifies an
isomorphism of its generic fibre with `S` and proves that this isomorphism
identifies the generic inclusion with the original `iS`. The record
`UnitFixedIntegralTorusData` retains all these maps and properties.

The proof sends source units into the ambient character kernel by
`IntegerValuation.map_mem_characterValuationKernel`; the unit-fixed
assumption puts their images into the pointwise fixer. The residue field
of the maximal-unramified integers is algebraically closed, hence infinite.
Their units have valuation one, using the comparison of the integer
valuation with `fixedFieldValuation`.

`IntegralModel.SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_baseChange`
then extends `S` as a closed split torus of the full model. Its intersection
hypothesis is supplied by
`IntegralModel.unramifiedIntegerRange_intersection`. Split tori have
geometrically connected fibres by `IsSplitTorus.isReductive`, so
`RelativeIdentityComponent.factor` factors this inclusion through the
supplied relative component. The factor remains closed by
`IsRelativeIdentityComponent.isClosedSubgroup_of_comp`. Finally the
compatible generic square of `N.inclusion` proves the stated square for
the neutral model.

This is a derived construction from the named published Library inputs.
It does not choose a containing residue maximal torus or assert an
apartment conclusion.
