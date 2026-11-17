# Vector-bundle series for supplied radicals in split dynamic charts

This derived unit works over the spectrum of an arbitrary commutative ring.
The ambient group is reductive and has a supplied fibrewise maximal coordinate
split torus, a finite fibrewise root datum and actual root parametrizations.
A parabolic inclusion represents the dynamic parabolic of a specified
coordinate cocharacter. The input radical is any supplied homomorphism
`r : U → P` satisfying the full `IsRelativeUnipotentRadical` predicate.

`splitDynamicRadicalWeightIso` composes the adapted chart's positive-weight
comparison with the published comparison between every supplied relative
radical and the actual dynamic contracting group. The result is an isomorphism
from the actual chart weight-cutoff-one group to the supplied group `U`.
`splitDynamicRadicalWeightIso_hom_comp` proves that its ambient composite is
exactly the chart's original positive-weight inclusion.

`hasFiniteVectorBundleSeries_relativeRadical_of_splitDynamic` first obtains
the finite series for the actual contracting group. The published dynamic
relative Levi and radical identification theorems say that `r` followed by
the parabolic inclusion represents the same contracting functor on all
scheme tests. Transport between these representatives proves the series
for the supplied `U`.

`hasFiniteVectorBundleSeries_relativeRadical_of_local_splitDynamic` uses
the existing actual root-family construction over arbitrary local rings
to discharge the root-parametrization input. No reducedness, noetherian
or field hypothesis is imposed on the ring.

Provenance is the existing split contracting-group series, dynamic relative
Levi theorem, supplied-radical comparison and series transport. This unit
does not construct a split dynamic presentation of an arbitrary parabolic,
nor compatibility or descent of the series over a cover.
