# Conditional reduction for spherical tempered standard modules

Author: Worker 1761.

This module proves a conditional reduction to the two obligations in
`SphericalStandardModulePrerequisites`. It does not prove either obligation
or the unconditional `SphericalTemperedStandardModuleStatement`.
Its provenance is internal composition of published constituent uniqueness,
existence, exactness of compact fixed vectors, and actual representation maps.

`exists_ordered_sphericalConstituent` starts with the tuple witnessing the
supplied spherical spectrum. It sorts the tuple by its complex norms.
Permutation preserves the unordered spectrum, including multiplicities.
The published existence theorem provides a spherical constituent for the
sorted tuple in the independently prescribed carrier universe. The published
constituent uniqueness theorem identifies it with the original object.
Transport along that actual equivalence shows that the original object is
a constituent for the sorted tuple. This argument does not interchange
the inducing characters by an equivalence of principal series.

`exists_principalSeries_quotient_of_generation` assumes ordered spherical
generation. Unpack the actual subquotient as a surjection from an invariant
subspace. Its representation is smooth by injective transfer. A nonzero
maximal-compact fixed vector of the target lifts to a fixed vector of that
subspace by the published compact averaging theorem
`Unramified.exists_fixed_lift`. Its image is nonzero, so the lift is nonzero.
The generation hypothesis forces the subspace to equal the whole principal
series. The usual equivalence between the top subrepresentation and its
ambient representation then gives an actual surjective intertwiner from the
full principal series. This helper permits an independent target universe
and does not require the target to be irreducible.

`sphericalTemperedStandardModule_of_prerequisites` applies these two helpers,
then invokes the assumed ordered tempered realization to choose a datum and
an actual equivalence from its standard module to the ordered principal
series. Compose that equivalence, the resulting principal-series quotient,
and the inverse of the supplied equivalence between `J` and `A`. The composite
is a surjective intertwiner onto `J`. Equivalence transports the supplied
irreducibility of `A` to `J`, establishing the required quotient relation.
The sorted tuple supplies the requested spectrum and weak norm order, and
the realization hypothesis supplies the requested standard-module equivalence.
The field and automorphic carrier universes remain independent throughout.
