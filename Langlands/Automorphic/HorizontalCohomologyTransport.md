# Full operator maps on actual horizontal cohomology representations

Author: Worker 2.

This internal construction specializes the published generic equivariant
horizontal-cohomology transport to actual `OperatorRealization F n` objects.
The number field `F : Type u` has arbitrary universe, the natural rank `n`
is positive, and coefficients are complex in the existing realization spaces.
Source and target share `F` and `n`. Every natural degree, including zero,
is allowed.

For `A : S.Intertwiner T`, `Intertwiner.horizontalCyclesMap A q` is a bundled
finite adelic intertwiner from `S.horizontalCyclesFiniteRepresentation q`
to `T.horizontalCyclesFiniteRepresentation q`.
`Intertwiner.horizontalCohomologyMap A q` is a bundled finite adelic
intertwiner from `S.horizontalCohomologyFiniteRepresentation q` to
`T.horizontalCohomologyFiniteRepresentation q`. These are the already
constructed representations on actual differential kernels and their quotients
by actual image boundaries. Boundaries in degree zero are zero. No cycle,
boundary, quotient or representation is replaced by another carrier.

Both maps specialize `Horizontal.mapCyclesIntertwiner` and
`Horizontal.mapCohomologyIntertwiner`. The shared horizontal data are
`compactInReducedSubmodule F n` and `reducedCompactRepresentation F n`.
The two coefficient actions are the actual `S.compactRepresentation` and
`T.compactRepresentation`. Bracket covariance is the Lie-equivalence law for
the actual reduced conjugation. The coefficient covariance and insertion
identities are the proved `compactRepresentation_reducedLieAction` and
`horizontalCochain_infinitesimal` of each realization, exactly as in the
existing actual horizontal complex.

The additional actions are `S.horizontalFiniteRepresentation` and
`T.horizontalFiniteRepresentation`, whose commutation with the differentials
is already proved by `horizontalDifferential_finite`. The cochain maps are
`A.horizontalMap`, constructed from the same full operator intertwiner `A`.
The private `horizontalMap_chain` restates the symmetry of
`A.horizontalMap_differential` in the notation expected by the generic
construction. Its proof explicitly unfolds `Horizontal.differential`, the
actual `horizontalDifferential`, and `horizontalEquivariantSubmodule` to
identify their definitionally identical carriers and differentials. No new
chain equation is an input.

Consequently the underlying cycle linear map is the published
`Horizontal.mapCycles` for the degreewise linear maps
`(A.horizontalMap q).toLinearMap`. The underlying quotient linear map is the
published `Horizontal.mapCohomology` for the same maps and chain equation.
The generic construction proves cycle and boundary preservation and finite
adelic equivariance. On a cycle it retains the same transported horizontal
cochain; on a class it descends that transport to the existing quotient.
Dedicated actual formula and functor-law declarations are separate work.

The five named local additive groups on the actual function spaces and the
two on `S.Space`, `T.Space` are exactly the canonical
`Submodule.addCommGroup` structures. The provenance is internal specialization
of `HorizontalCohomologyIntertwiner`, `HorizontalTransportCore` and
`HorizontalCohomologyFinite`; no new external-literature identification is
asserted. Full equivariance for every element of the standard infinite compact
group, including its disconnected components, is retained. This unit makes
no claim of whole-quotient smoothness, topology, finiteness, nonvanishing,
general coefficient attachment, sheaf or analytic comparison, or
relative-to-absolute injectivity.
