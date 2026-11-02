# Local-spectrum chart complexes and module homology retracts

This internal construction identifies coefficient complexes on the actual local
rational quotient spectrum with the complexes on its translated compact clopen
charts, and constructs their retraction from supported module homology.

## Inputs and size

The complete ultrametric field, presented strict affinoid algebra, topological
group, rational spectral action and varying-open-subgroup transport object are
those of `InducedRationalChartComplex`. Coefficients are smooth representations
over an arbitrary commutative ring, without a topology on their carriers. The
field, group, ring, coefficient-carrier and indexing universes are independent;
the coefficient complex and its shape are supplied.

`localSpectrumCoefficientFunctor` takes all locally constant functions from the
actual `X.LocalSpectrum`, with coefficient intertwiners applied pointwise. Its
module carrier universe is `max u w`. To compare it with functions on induced
charts, whose carrier universe is `max u v w`,
`liftedLocalSpectrumCoefficientFunctor` composes it with Mathlib's
`ModuleCat.uliftFunctor.{v}`. Its elements are explicitly `ULift` of the original
locally constant functions; `down` recovers each actual function. Both functors
are additive. No coefficient or group universe is identified with the field
universe.

## Coordinates, complexes and maps

`localChartCoefficientIso` uses the already constructed
`X.inducedChartHomeomorph a`. The forward map precomposes a lowered local function
with the inverse homeomorphism; the inverse precomposes a chart function with
the homeomorphism and lifts the resulting function. Both maps are linear and
natural in smooth coefficients. Their inverse identities are the homeomorphism
inverse identities evaluated inside a locally constant function.

`localSpectrumComplexFunctor` applies this lifted additive functor to every
term and differential of the supplied coefficient complex. Its differential,
after lowering, is the original coefficient differential applied pointwise.
Mathlib prolongation gives `localChartComplexIso`, a natural isomorphism with
the actual `chartComplexFunctor` for every translate.

`localChartComplexExtension` composes that coordinate isomorphism with the
previous chart zero extension. On each lowered function it is exactly the
existing `localChartExtension`. `localChartComplexRestriction` composes actual
chart restriction with inverse coordinates. Its evaluation at a local point
is the supported function evaluated at `X.inducedChart a` of that point.
Restriction after extension is the identity. Extension after restriction is
the previously constructed supported chart chain projection, so local
coordinates do not alter that projection.

## Actual module homology

`supportedModuleHomologyFunctor`, `chartHomologyFunctor` and
`localSpectrumHomologyFunctor` take categorical homology of these particular
module complexes. `localChartHomologyIso` is the induced homology isomorphism
from the actual chain isomorphism. Applying the same homology functor to local
extension and restriction gives `localChartHomologyExtension` and
`localChartHomologyRestriction`. Functoriality carries their chain retraction
to a retraction on module homology. Their composite in the other order is
`chartHomologyProjection`, the induced map of the original chain projection.
Functoriality proves its idempotence. Preservation of zero by the additive
homology functor proves orthogonality for distinct actual coset components.

These are module homology constructions. Individual charts need not be
preserved by the full group, so no full-group equivariance is asserted for
these maps. Although the supported module complex is the underlying supported
smooth complex, this file makes no identification of module homology with
the underlying smooth homology.

## Provenance and remaining obligations

This is an internal derivation from the actual chart homeomorphisms and
supported chart chain maps, and pinned Mathlib's module universe lift,
additive prolongation and categorical homology functors. Every map is
constructed from those functions and functors, with inverse, naturality,
chain-map and retraction obligations proved. No new original-literature
assertion is added. Exactness of the supported coefficient functor, comparison
with the input coefficient homology, the smooth/module homology comparison,
analytic or etale sheaf comparison, a geometric or Godement resolution,
arithmetic coefficients, towers and Harris specialization remain separate
obligations.
