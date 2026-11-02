# Actual charts in degree-zero smooth cohomology

This internal construction transports the existing actual chart maps through
the proved degree-zero compact-function identifications. The two concrete
consumers are smooth Godement compact cohomology and right derived compact
sections of the full locally constant smooth sheaf on `X.InducedSpectrum`.
The field, group, coefficient ring and coefficient carriers share universe `u`.
The field is complete and nonarchimedean; the ring is commutative and the group
is a topological group. For both cohomological consumers, stable neighborhoods
on the actual induced spectrum remain an explicit hypothesis.

`godementZeroModuleFunctor` and `compactDerivedZeroModuleFunctor` forget the
group action on the actual degree-zero cohomology objects. Their natural
isomorphisms identify them with `CompactSections.supportedModuleFunctor X`.
They retain every compact function. A fixed chart is moved by the full group,
so the individual chart maps here are module morphisms.

The namespace `Charts` implements the same construction for either of these
natural isomorphisms. `extension` extends a function on the compact clopen
chart by zero and applies the inverse degree-zero isomorphism. `restriction`
applies the forward isomorphism and restricts to that actual chart. Their
composite on the chart is the identity. The opposite composite `projection`
corresponds under the forward isomorphism to the original `chartPart`.
Consequently it is idempotent, and projections for distinct coset components
are orthogonal.

`componentSupport` is the set of nonzero coset components of the corresponding
compact function. It is finite. `sum_projection_eq` reconstructs a cohomology
vector from any finite set containing those actual components.
`exists_sum_projection` obtains such a set for every vector separately.
There is no asserted support bound uniform in all vectors.

`localExtension` and `localRestriction` compose the chart maps with the existing
natural isomorphism defined by the constructed homeomorphism from the local
rational spectrum to the chart. The existing `ULift` in its coefficient
functor is retained. Their composite on local-spectrum functions is the
identity, and their opposite composite is exactly `projection`.
The proved application formulas identify the extension with the original
`CompactSections.localChartExtension` and evaluate restriction at
`X.inducedChart a z`.

The named Godement and derived extension/restriction maps instantiate these
constructions. `godementDerivedZeroModuleIso` compares the two realizations
through their full compact-function identifications. The proved chart
extension and restriction equations show that this comparison respects the
actual chart maps. `godementDerivedZeroModuleIso_eq` proves that this is exactly
the original degree-zero comparison with the group action forgotten.

The provenance is internal composition of the existing induced rational
charts, compact-function chart maps and degree-zero natural isomorphisms.
The proofs use their inverse laws, the original finite chart decomposition
and the constructed local chart homeomorphism. No higher cohomological chart
comparison, higher Godement/derived comparison, analytic or etale
identification, or Harris specialization is asserted.
